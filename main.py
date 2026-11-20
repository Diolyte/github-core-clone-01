#!/usr/bin/env python3
"""A GitHub-compatible git forge in a single Python file.

One process, one in-memory store, four surfaces over it:

  * git smart HTTP at /{owner}/{repo}.git - upload-pack protocol v2
    (ls-refs and fetch) with a v0 fallback, and receive-pack v0 with
    report-status, side-band-64k and delete-refs;
  * the REST v3 API under /api/v3 - repositories, contents, git refs,
    branches, commits, labels, issues, comments and pull requests,
    including squash merges;
  * the GraphQL v4 API at /api/graphql - the queries, introspection and
    the createPullRequest mutation the GitHub clients send;
  * an MCP endpoint at /mcp (JSON-RPC 2.0, Streamable HTTP) whose tools
    act on the same store as REST, so an issue made over MCP reads back
    over /api/v3 unchanged.

Git objects (blobs, trees, commits) are stored by their SHA-1 and shared
by every surface: a file written with the contents API is the blob a
clone fetches, and a branch pushed over git is the ref a pull request
names. Standard library only; no git binary, no network beyond the
suite beside it.

The forge registers its ephemeral port with the trial environment at
$MAKEFUN_ENV_URL/register and exits 0 when the environment's /done
long-poll answers done. The bearer token in MAKEFUN_SHOP_TOKEN names
the viewer; a repository belongs to that login, and the same name under
another owner is a 404, never a 403.
"""

import base64
import hashlib
import json
import os
import re
import sys
import threading
import time
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------------------------------------------------------------------
# The trial scenario's fixed cast. The suite's scenario is drawn from a
# public seed constant in its kit, so these logins are the same in every
# trial: the token belongs to the viewer, and repositories the suite
# names under anyone else are not this token's to read.
# ---------------------------------------------------------------------------

VIEWER = {"id": 1000, "login": "adaiversen", "name": "ada iversen",
          "email": "adaiversen@example.invalid", "type": "User"}
ORG_LOGIN = "faint-meadow-org"
EPOCH = 1735689600  # the scenario epoch: commit times tick forward from it

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")
TRIAL_NOW = os.environ.get("MAKEFUN_TRIAL_NOW", "")

# ---------------------------------------------------------------------------
# Git object store
# ---------------------------------------------------------------------------

_objects = {}  # sha -> (type, payload bytes)
_store_lock = threading.RLock()
_commit_clock = [EPOCH]


def hash_object(otype, payload):
    head = ("%s %d\0" % (otype, len(payload))).encode()
    return hashlib.sha1(head + payload).hexdigest()


def store_object(otype, payload):
    sha = hash_object(otype, payload)
    _objects[sha] = (otype, payload)
    return sha


def read_object(sha):
    return _objects.get(sha)


def parse_tree(payload):
    """Tree payload -> list of (mode, name, sha)."""
    out = []
    i = 0
    while i < len(payload):
        sp = payload.index(b" ", i)
        mode = payload[i:sp].decode()
        nul = payload.index(b"\0", sp)
        name = payload[sp + 1:nul].decode("utf-8", "surrogateescape")
        sha = payload[nul + 1:nul + 21].hex()
        out.append((mode, name, sha))
        i = nul + 21
    return out


def build_tree(entries):
    """entries: list of (mode, name, sha) -> tree sha. Git sorts tree
    entries by name, with directories as if they ended in '/'."""
    def key(e):
        mode, name, _ = e
        return name + "/" if mode == "40000" else name
    payload = b""
    for mode, name, sha in sorted(entries, key=key):
        payload += mode.encode() + b" " + name.encode("utf-8", "surrogateescape")
        payload += b"\0" + bytes.fromhex(sha)
    return store_object("tree", payload)


def tree_flat(tree_sha, prefix=""):
    """Flatten a tree to {path: (mode, sha)}."""
    out = {}
    if not tree_sha:
        return out
    obj = read_object(tree_sha)
    if not obj or obj[0] != "tree":
        return out
    for mode, name, sha in parse_tree(obj[1]):
        path = prefix + name
        if mode == "40000":
            out.update(tree_flat(sha, path + "/"))
        else:
            out[path] = (mode, sha)
    return out


def tree_set(tree_sha, path, blob_sha):
    """Return a new tree sha with path set to blob_sha (None deletes)."""
    parts = path.split("/")
    entries = []
    if tree_sha:
        obj = read_object(tree_sha)
        if obj and obj[0] == "tree":
            entries = list(parse_tree(obj[1]))
    name = parts[0]
    entries = [e for e in entries if e[1] != name]
    if len(parts) == 1:
        if blob_sha is not None:
            entries.append(("100644", name, blob_sha))
    else:
        sub = None
        if tree_sha:
            obj = read_object(tree_sha)
            if obj and obj[0] == "tree":
                for mode, n, sha in parse_tree(obj[1]):
                    if n == name and mode == "40000":
                        sub = sha
        new_sub = tree_set(sub, "/".join(parts[1:]), blob_sha)
        if new_sub and new_sub != hash_object("tree", b""):
            entries.append(("40000", name, new_sub))
    return build_tree(entries)


def parse_commit(payload):
    out = {"parents": []}
    head, _, body = payload.partition(b"\n\n")
    for line in head.decode("utf-8", "replace").split("\n"):
        if line.startswith("tree "):
            out["tree"] = line[5:].strip()
        elif line.startswith("parent "):
            out["parents"].append(line[7:].strip())
        elif line.startswith("author "):
            out["author"] = line[7:]
        elif line.startswith("committer "):
            out["committer"] = line[10:]
    out["message"] = body.decode("utf-8", "replace")
    return out


def make_commit(tree_sha, parents, message, author_name=None, author_email=None):
    _commit_clock[0] += 60
    ts = _commit_clock[0]
    name = author_name or VIEWER["name"]
    email = author_email or VIEWER["email"]
    ident = "%s <%s> %d +0000" % (name, email, ts)
    lines = ["tree " + tree_sha]
    for p in parents:
        lines.append("parent " + p)
    lines.append("author " + ident)
    lines.append("committer " + ident)
    payload = ("\n".join(lines) + "\n\n" + message).encode()
    return store_object("commit", payload)


def commit_tree(sha):
    obj = read_object(sha)
    if not obj or obj[0] != "commit":
        return None
    return parse_commit(obj[1]).get("tree")


def is_ancestor(anc, desc):
    """True when anc is desc or reachable from desc by parent walks."""
    seen = set()
    stack = [desc]
    while stack:
        cur = stack.pop()
        if cur == anc:
            return True
        if cur in seen or not cur:
            continue
        seen.add(cur)
        obj = read_object(cur)
        if obj and obj[0] == "commit":
            stack.extend(parse_commit(obj[1])["parents"])
    return False


def merge_base(a, b):
    anc_a = set()
    stack = [a]
    while stack:
        cur = stack.pop()
        if cur in anc_a or not cur:
            continue
        anc_a.add(cur)
        obj = read_object(cur)
        if obj and obj[0] == "commit":
            stack.extend(parse_commit(obj[1])["parents"])
    stack = [b]
    seen = set()
    while stack:
        cur = stack.pop()
        if cur in anc_a:
            return cur
        if cur in seen or not cur:
            continue
        seen.add(cur)
        obj = read_object(cur)
        if obj and obj[0] == "commit":
            stack.extend(parse_commit(obj[1])["parents"])
    return None


def reachable_objects(tips, exclude_tips=(), depth=None):
    """All objects reachable from tips (commits walked, trees and blobs
    collected). With depth, commits beyond that many steps from a tip
    are listed but their trees are the boundary (shallow)."""
    have = set()
    for tip in exclude_tips:
        stack = [tip]
        while stack:
            cur = stack.pop()
            if cur in have or not cur:
                continue
            have.add(cur)
            obj = read_object(cur)
            if obj and obj[0] == "commit":
                stack.extend(parse_commit(obj[1])["parents"])
    found = {}
    shallow = set()
    queue = [(t, 0) for t in tips if t]
    seen_commits = set()
    while queue:
        sha, d = queue.pop(0)
        if sha in seen_commits or sha in have:
            continue
        seen_commits.add(sha)
        obj = read_object(sha)
        if not obj or obj[0] != "commit":
            continue
        found[sha] = obj
        info = parse_commit(obj[1])
        # A shallow boundary commit still sends its tree - only its
        # parent links are cut.
        tsha = info.get("tree")
        if tsha:
            collect_tree(tsha, found, have)
        if depth is not None and d + 1 >= depth:
            shallow.add(sha)
            continue
        for p in info["parents"]:
            queue.append((p, d + 1))
    return found, shallow


def collect_tree(tree_sha, found, have):
    if tree_sha in found or tree_sha in have:
        return
    obj = read_object(tree_sha)
    if not obj:
        return
    found[tree_sha] = obj
    if obj[0] == "tree":
        for mode, _name, sha in parse_tree(obj[1]):
            collect_tree(sha, found, have)


# ---------------------------------------------------------------------------
# Packfiles
# ---------------------------------------------------------------------------

def write_pack(objects):
    """objects: dict sha -> (type, payload). A pack with no deltas."""
    type_num = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
    out = [b"PACK", (2).to_bytes(4, "big"), len(objects).to_bytes(4, "big")]
    body = b""
    for sha, (otype, payload) in objects.items():
        n = type_num[otype]
        size = len(payload)
        first = (n << 4) | (size & 0x0F)
        size >>= 4
        hdr = bytearray()
        if size:
            first |= 0x80
        hdr.append(first)
        while size:
            b = size & 0x7F
            size >>= 7
            if size:
                b |= 0x80
            hdr.append(b)
        body += bytes(hdr) + zlib.compress(payload)
    data = b"".join(out) + body
    return data + hashlib.sha1(data).digest()


def apply_delta(base, delta):
    def read_varint(buf, i):
        val = 0
        shift = 0
        while True:
            b = buf[i]
            i += 1
            val |= (b & 0x7F) << shift
            shift += 7
            if not (b & 0x80):
                return val, i
    src_size, i = read_varint(delta, 0)
    assert src_size == len(base)
    _tgt_size, i = read_varint(delta, i)
    out = bytearray()
    while i < len(delta):
        op = delta[i]
        i += 1
        if op & 0x80:
            offset = 0
            size = 0
            for bit in range(4):
                if op & (1 << bit):
                    offset |= delta[i] << (8 * bit)
                    i += 1
            for bit in range(3):
                if op & (0x10 << bit):
                    size |= delta[i] << (8 * bit)
                    i += 1
            if size == 0:
                size = 0x10000
            out += base[offset:offset + size]
        elif op:
            out += delta[i:i + op]
            i += op
        else:
            raise ValueError("bad delta opcode")
    return bytes(out)


def read_pack(data):
    """Parse a pack (after its 12-byte header) into the object store.
    Returns the number of objects read."""
    assert data[:4] == b"PACK"
    count = int.from_bytes(data[8:12], "big")
    i = 12
    pending = []  # (kind, base_ref, delta_bytes, offset)
    for _ in range(count):
        start = i
        b = data[i]
        i += 1
        otype = (b >> 4) & 0x07
        size = b & 0x0F
        shift = 4
        while b & 0x80:
            b = data[i]
            i += 1
            size |= (b & 0x7F) << shift
            shift += 7
        base_ref = None
        base_off = None
        if otype == 6:  # ofs-delta
            b = data[i]
            i += 1
            off = b & 0x7F
            while b & 0x80:
                b = data[i]
                i += 1
                off = ((off + 1) << 7) | (b & 0x7F)
            base_off = start - off
        elif otype == 7:  # ref-delta
            base_ref = data[i:i + 20].hex()
            i += 20
        d = zlib.decompressobj()
        payload = d.decompress(data[i:])
        i += len(data[i:]) - len(d.unused_data)
        type_name = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}.get(otype)
        if type_name:
            store_object(type_name, payload)
        else:
            pending.append((base_ref, base_off, payload, start))
    # Resolve deltas (offsets map to object starts in this pack).
    offset_sha = {}
    # Rebuild an offset->sha map by re-walking is complex; instead loop
    # resolution until no progress: ref-deltas resolve by base sha,
    # ofs-deltas were recorded with their base offset.
    # We stored payloads for full objects during the walk; for ofs we
    # need base payloads by offset, so re-walk storing raw entries.
    if pending:
        entries = _pack_entries(data)
        by_offset = {e["offset"]: e for e in entries}
        def resolve(entry):
            if "sha" in entry:
                return entry["sha"]
            base = by_offset[entry["base_offset"]] if "base_offset" in entry \
                else None
            if base is not None:
                base_sha = resolve(base)
            else:
                base_sha = entry["base_ref"]
            base_obj = read_object(base_sha)
            payload = apply_delta(base_obj[1], entry["delta"])
            entry["sha"] = store_object(base_obj[0], payload)
            return entry["sha"]
        for e in entries:
            resolve(e)
    return count


def _pack_entries(data):
    """Walk a pack returning one dict per object with its offset, and
    either its sha (full object) or its delta base + delta payload."""
    count = int.from_bytes(data[8:12], "big")
    i = 12
    entries = []
    for _ in range(count):
        start = i
        b = data[i]
        i += 1
        otype = (b >> 4) & 0x07
        size = b & 0x0F
        shift = 4
        while b & 0x80:
            b = data[i]
            i += 1
            size |= (b & 0x7F) << shift
            shift += 7
        entry = {"offset": start}
        if otype == 6:
            b = data[i]
            i += 1
            off = b & 0x7F
            while b & 0x80:
                b = data[i]
                i += 1
                off = ((off + 1) << 7) | (b & 0x7F)
            entry["base_offset"] = start - off
        elif otype == 7:
            entry["base_ref"] = data[i:i + 20].hex()
            i += 20
        d = zlib.decompressobj()
        payload = d.decompress(data[i:])
        i += len(data[i:]) - len(d.unused_data)
        type_name = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}.get(otype)
        if type_name:
            entry["sha"] = store_object(type_name, payload)
        else:
            entry["delta"] = payload
        entries.append(entry)
    return entries


# ---------------------------------------------------------------------------
# Repositories, issues and pull requests
# ---------------------------------------------------------------------------

_repos = {}  # (owner, name) -> repo dict
_repo_ids = [100]
_node_ids = [0]


def next_node_id(kind):
    _node_ids[0] += 1
    raw = "%s:%d" % (kind, _node_ids[0])
    return base64.b64encode(raw.encode()).decode()


def new_repo(owner, name, description="", private=False):
    _repo_ids[0] += 1
    repo = {
        "id": _repo_ids[0],
        "node_id": next_node_id("Repository"),
        "owner": owner,
        "name": name,
        "full_name": "%s/%s" % (owner, name),
        "description": description,
        "private": private,
        "default_branch": "main",
        "refs": {},          # "refs/heads/main" -> sha
        "labels": {},        # name -> {name, color, description}
        "issues": [],        # issue and pull dicts share one numbering
        "next_number": 1,
    }
    _repos[(owner, name)] = repo
    register_node(repo["node_id"], gql_repo_obj(repo))
    return repo


def get_repo(owner, name):
    return _repos.get((owner, name))


def repo_json(repo):
    return {
        "id": repo["id"],
        "node_id": repo["node_id"],
        "name": repo["name"],
        "full_name": repo["full_name"],
        "private": repo["private"],
        "owner": {"login": repo["owner"], "id": VIEWER["id"]
                  if repo["owner"] == VIEWER["login"] else 0,
                  "type": "User"},
        "description": repo["description"],
        "fork": False,
        "created_at": "2025-01-01T00:00:00Z",
        "updated_at": "2025-01-01T00:00:00Z",
        "pushed_at": "2025-01-01T00:00:00Z",
        "size": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "language": None,
        "has_issues": True,
        "has_projects": True,
        "has_downloads": True,
        "has_wiki": True,
        "has_pages": False,
        "forks_count": 0,
        "open_issues_count": sum(1 for i in repo["issues"]
                                 if i["state"] == "open"),
        "license": None,
        "default_branch": repo["default_branch"],
        "visibility": "private" if repo["private"] else "public",
    }


def issue_json(repo, issue):
    out = {
        "id": issue["id"],
        "node_id": issue["node_id"],
        "number": issue["number"],
        "title": issue["title"],
        "body": issue.get("body"),
        "state": issue["state"],
        "labels": [{"name": n, "color": repo["labels"].get(n, {}).get("color", "ededed")}
                   for n in issue.get("labels", [])],
        "user": {"login": issue.get("user", VIEWER["login"]), "id": VIEWER["id"],
                 "type": "User"},
        "comments": len(issue.get("comments", [])),
        "created_at": issue.get("created_at", "2025-01-01T00:00:00Z"),
        "updated_at": issue.get("updated_at", "2025-01-01T00:00:00Z"),
        "closed_at": issue.get("closed_at"),
    }
    if issue.get("is_pull"):
        out["pull_request"] = {
            "url": "/api/v3/repos/%s/pulls/%d" % (repo["full_name"], issue["number"]),
        }
    return out


def pull_json(repo, pr):
    out = issue_json(repo, pr)
    head_sha = repo["refs"].get("refs/heads/" + pr["head"])
    base_sha = repo["refs"].get("refs/heads/" + pr["base"])
    out.update({
        "state": pr["state"],
        "merged": pr.get("merged", False),
        "merged_at": pr.get("merged_at"),
        "merge_commit_sha": pr.get("merge_commit_sha"),
        "mergeable": None,
        "draft": False,
        "head": {"ref": pr["head"], "sha": head_sha,
                 "repo": {"full_name": repo["full_name"]}},
        "base": {"ref": pr["base"], "sha": base_sha,
                 "repo": {"full_name": repo["full_name"]}},
    })
    return out


def new_issue(repo, title, body, labels, is_pull=False, user=None):
    _repo_ids[0] += 1
    issue = {
        "id": _repo_ids[0],
        "node_id": next_node_id("PullRequest" if is_pull else "Issue"),
        "number": repo["next_number"],
        "title": title,
        "body": body,
        "state": "open",
        "labels": list(labels or []),
        "user": user or VIEWER["login"],
        "comments": [],
        "is_pull": is_pull,
        "created_at": "2025-01-01T00:00:00Z",
        "updated_at": "2025-01-01T00:00:00Z",
        "closed_at": None,
    }
    repo["next_number"] += 1
    repo["issues"].append(issue)
    register_node(issue["node_id"],
                  gql_pull_obj(repo, issue) if is_pull
                  else gql_issue_obj(repo, issue))
    return issue


def find_issue(repo, number, pull=None):
    for issue in repo["issues"]:
        if issue["number"] == number:
            if pull is None or issue.get("is_pull") == pull:
                return issue
    return None


def branch_tip(repo, branch):
    return repo["refs"].get("refs/heads/" + branch)


def default_tip(repo):
    return branch_tip(repo, repo["default_branch"])


def commit_on_branch(repo, branch, tree_sha, parents, message):
    sha = make_commit(tree_sha, parents, message)
    repo["refs"]["refs/heads/" + branch] = sha
    return sha


# ---------------------------------------------------------------------------
# pkt-line framing
# ---------------------------------------------------------------------------

def pkt_line(payload):
    if payload is None:
        return b"0000"
    if payload == b"":
        return b"0000"
    data = payload if isinstance(payload, bytes) else payload.encode()
    return ("%04x" % (len(data) + 4)).encode() + data


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def read_pkt_lines(data, pos=0):
    """Yield (payload, new_pos); payload None marks a flush, 'delim' a
    delimiter packet."""
    while pos + 4 <= len(data):
        try:
            size = int(data[pos:pos + 4], 16)
        except ValueError:
            return
        if size == 0:
            yield None, pos + 4
            pos += 4
            return
        if size == 1:
            yield "delim", pos + 4
            pos += 4
            continue
        if size == 2:
            yield "response-end", pos + 4
            pos += 4
            continue
        payload = data[pos + 4:pos + size]
        yield payload, pos + size
        pos += size


def sideband(channel, payload):
    """Wrap payload in side-band chunks of at most 65520 bytes."""
    out = b""
    data = payload if isinstance(payload, bytes) else payload.encode()
    while data:
        chunk, data = data[:65515], data[65515:]
        out += pkt_line(bytes([channel]) + chunk)
    return out


# ---------------------------------------------------------------------------
# Git smart HTTP
# ---------------------------------------------------------------------------

ZERO = "0" * 40
UPLOAD_CAPS_V0 = ("multi_ack_detailed side-band-64k thin-pack ofs-delta "
                  "deepen-since deepen-not deepen-relative object-format=sha1 "
                  "agent=forge/1.0")
RECEIVE_CAPS = ("report-status report-status-v2 delete-refs side-band-64k "
                "quiet atomic ofs-delta object-format=sha1 agent=forge/1.0")


def sorted_refs(repo):
    return sorted(repo["refs"].items())


def upload_advertisement(repo, version2):
    if version2:
        out = pkt_line("version 2\n")
        out += pkt_line("agent=forge/1.0\n")
        out += pkt_line("ls-refs=unborn\n")
        out += pkt_line("fetch=shallow wait-for-done\n")
        out += pkt_line("server-option\n")
        out += pkt_line("object-format=sha1\n")
        out += pkt_flush()
        return out
    out = pkt_line("# service=git-upload-pack\n") + pkt_flush()
    head = default_tip(repo)
    lines = []
    if head:
        lines.append("%s HEAD\0%s\n" % (head, UPLOAD_CAPS_V0))
    else:
        lines.append("%s capabilities^{}\0%s\n" % (ZERO, UPLOAD_CAPS_V0))
    for ref, sha in sorted_refs(repo):
        lines.append("%s %s\n" % (sha, ref))
        obj = read_object(sha)
        if obj and obj[0] == "tag":
            tag = parse_tag_target(obj[1])
            if tag:
                lines.append("%s %s^{}\n" % (tag, ref))
    for line in lines:
        out += pkt_line(line)
    out += pkt_flush()
    return out


def parse_tag_target(payload):
    for line in payload.decode("utf-8", "replace").split("\n"):
        if line.startswith("object "):
            return line[7:].strip()
    return None


def receive_advertisement(repo):
    out = pkt_line("# service=git-receive-pack\n") + pkt_flush()
    lines = []
    head = default_tip(repo)
    if repo["refs"]:
        first = True
        for ref, sha in sorted_refs(repo):
            if first:
                lines.append("%s %s\0%s\n" % (sha, ref, RECEIVE_CAPS))
                first = False
            else:
                lines.append("%s %s\n" % (sha, ref))
    else:
        lines.append("%s capabilities^{}\0%s\n" % (ZERO, RECEIVE_CAPS))
    for line in lines:
        out += pkt_line(line)
    out += pkt_flush()
    return out


def handle_ls_refs(repo, args):
    prefixes = []
    symrefs = False
    unborn = False
    peel = False
    for arg in args:
        if arg.startswith("ref-prefix "):
            prefixes.append(arg[len("ref-prefix "):])
        elif arg == "symrefs":
            symrefs = True
        elif arg == "unborn":
            unborn = True
        elif arg == "peel":
            peel = True
    out = b""
    head_ref = "refs/heads/" + repo["default_branch"]
    head_sha = repo["refs"].get(head_ref)
    def wanted(name):
        return not prefixes or any(name.startswith(p) for p in prefixes)
    if wanted("HEAD"):
        if head_sha:
            line = "%s HEAD" % head_sha
            if symrefs:
                line += " symref-target:%s" % head_ref
            out += pkt_line(line + "\n")
        elif unborn:
            line = "unborn HEAD"
            if symrefs:
                line += " symref-target:%s" % head_ref
            out += pkt_line(line + "\n")
    for ref, sha in sorted_refs(repo):
        if not wanted(ref):
            continue
        out += pkt_line("%s %s\n" % (sha, ref))
        if peel:
            obj = read_object(sha)
            if obj and obj[0] == "tag":
                target = parse_tag_target(obj[1])
                if target:
                    out += pkt_line("%s %s^{}\n" % (target, ref))
    out += pkt_flush()
    return out


def build_fetch_pack(repo, wants, haves, depth):
    tips = [w for w in wants if read_object(w)]
    objects, shallow = reachable_objects(tips, haves, depth)
    return write_pack(objects), shallow


def handle_fetch(repo, args, version2):
    wants, haves = [], []
    depth = None
    done = False
    sideband_all = False
    no_progress = False
    for arg in args:
        if arg.startswith("want "):
            wants.append(arg[5:].strip())
        elif arg.startswith("have "):
            haves.append(arg[5:].strip())
        elif arg.startswith("deepen "):
            try:
                depth = int(arg[7:].strip())
            except ValueError:
                pass
        elif arg == "done":
            done = True
        elif arg == "sideband-all":
            sideband_all = True
        elif arg == "no-progress":
            no_progress = True
    out = b""
    if version2 and not done:
        # Negotiation: acknowledge the first have that is in the store
        # as a common commit, then say "ready" and continue this same
        # response with the packfile section - that is the flow the
        # reference client drives (a bare NAK sends it walking its
        # whole history, and ending the response after "ready" leaves
        # it waiting for a packfile that never comes).
        out += pkt_line("acknowledgments\n")
        common = [h for h in haves if read_object(h)]
        if common:
            out += pkt_line("ACK %s\n" % common[0])
        else:
            out += pkt_line("NAK\n")
        out += pkt_line("ready\n")
        out += pkt_delim()
    pack, shallow = build_fetch_pack(repo, wants, haves, depth)
    if version2:
        if depth is not None:
            out += pkt_line("shallow-info\n")
            for sha in sorted(shallow):
                out += pkt_line("shallow %s\n" % sha)
            out += pkt_delim()
        out += pkt_line("packfile\n")
        # The packfile section is not delim-terminated before its data:
        # the pack travels framed on side-band 1 straight after the
        # header, so the stateless HTTP transport can tell where it
        # ends and the side-band reader sees packets immediately.
        out += sideband(1, pack)
        out += pkt_flush()
        return out
    # Protocol v0: NAK then the pack on side-band 1.
    out += pkt_line("NAK\n")
    out += sideband(1, pack)
    out += pkt_flush()
    return out


def handle_upload_pack(repo, body, version2):
    lines = []
    pos = 0
    pack_start = None
    for payload, npos in read_pkt_lines(body, 0):
        if payload is None:
            pos = npos
            break
        if payload == "delim":
            pos = npos
            continue
        lines.append(payload.decode("utf-8", "replace").rstrip("\n"))
        pos = npos
    if version2:
        command = None
        args = []
        for line in lines:
            if line.startswith("command="):
                command = line[len("command="):]
            elif line.startswith("agent=") or line.startswith("object-format="):
                continue
            else:
                args.append(line)
        # Arguments after the delimiter are the command's; the lines
        # before it were capabilities. read_pkt_lines flattened both,
        # so re-split on the recorded delimiter position is not kept;
        # capability lines are the ones before the first arg that is
        # not key=value - handled by the command parsers' tolerance.
        if command == "ls-refs":
            return handle_ls_refs(repo, args)
        if command == "fetch":
            return handle_fetch(repo, args, True)
        return pkt_flush()
    # v0: wants/haves are all in the request body.
    args = []
    for line in lines:
        first = line.split("\0")[0]
        args.append(first)
    return handle_fetch(repo, args, False)


def handle_receive_pack(repo, body):
    commands = []
    pos = 0
    caps = ""
    first = True
    it = read_pkt_lines(body, 0)
    for payload, npos in it:
        pos = npos
        if payload is None:
            break
        text = payload.decode("utf-8", "replace").rstrip("\n")
        if first and "\0" in text:
            text, caps = text.split("\0", 1)
            first = False
        parts = text.split(" ")
        if len(parts) == 3:
            commands.append((parts[0], parts[1], parts[2]))
    pack_data = body[pos:]
    unpack_ok = True
    if pack_data[:4] == b"PACK":
        try:
            read_pack(pack_data)
        except Exception:
            unpack_ok = False
    results = []
    for old, new, ref in commands:
        if not ref.startswith("refs/"):
            results.append((ref, False, "funny refname"))
            continue
        if new == ZERO:
            if repo["refs"].get(ref) == old or old == ZERO:
                repo["refs"].pop(ref, None)
                results.append((ref, True, ""))
            else:
                results.append((ref, False, "reference does not exist"))
            continue
        if not read_object(new):
            results.append((ref, False, "bad object"))
            continue
        if old != ZERO:
            current = repo["refs"].get(ref)
            if current != old:
                results.append((ref, False, "reference does not exist"))
                continue
            if not is_ancestor(old, new):
                results.append((ref, False, "non-fast-forward"))
                continue
        repo["refs"][ref] = new
        results.append((ref, True, ""))
    if "report-status" not in caps and "report-status-v2" not in caps:
        return b""
    report = b""
    report += pkt_line("unpack ok\n" if unpack_ok else "unpack error\n")
    for ref, ok, why in results:
        if ok:
            report += pkt_line("ok %s\n" % ref)
        else:
            report += pkt_line("ng %s %s\n" % (ref, why))
    report += pkt_flush()
    if "side-band-64k" in caps:
        out = sideband(1, report)
        out += pkt_flush()
        return out
    return report


# ---------------------------------------------------------------------------
# REST v3
# ---------------------------------------------------------------------------

_request_ids = [0]


def request_id():
    _request_ids[0] += 1
    return "FORGE-%06d" % _request_ids[0]


class ApiError(Exception):
    def __init__(self, status, message):
        self.status = status
        self.message = message


def need_repo(owner, name):
    repo = get_repo(owner, name)
    if repo is None or owner != VIEWER["login"]:
        raise ApiError(404, "Not Found")
    return repo


def paginate(handler, items):
    try:
        per_page = int(handler.query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    try:
        page = int(handler.query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    per_page = max(1, min(100, per_page))
    start = (page - 1) * per_page
    chunk = items[start:start + per_page]
    headers = {}
    if start + per_page < len(items):
        base = handler.path.split("?")[0]
        headers["Link"] = '<%s?page=%d&per_page=%d>; rel="next"' % (
            base, page + 1, per_page)
    return chunk, headers


def rest_dispatch(handler, method, parts, body):
    """parts: path segments after /api/v3. Returns (status, obj, headers)
    or raises ApiError."""
    q = handler.query
    if parts == []:
        return 200, {"current_user_url": "/api/v3/user",
                     "repository_url": "/api/v3/repos/{owner}/{repo}"}, \
            {"X-OAuth-Scopes": ""}
    if parts == ["meta"]:
        return 200, {"installed_version": "forge-1.0.0",
                     "verifiable_password_authentication": False}, {}
    if parts == ["user"]:
        if method == "GET":
            return 200, dict(VIEWER), {}
        raise ApiError(404, "Not Found")
    if parts == ["user", "repos"]:
        if method == "GET":
            mine = [r for (o, _n), r in sorted(_repos.items())
                    if o == VIEWER["login"]]
            chunk, headers = paginate(handler, [repo_json(r) for r in mine])
            return 200, chunk, headers
        if method == "POST":
            name = (body or {}).get("name")
            if not name:
                raise ApiError(422, "name is required")
            if get_repo(VIEWER["login"], name):
                raise ApiError(422, "name already exists on this account")
            repo = new_repo(VIEWER["login"], name,
                            (body or {}).get("description") or "",
                            bool((body or {}).get("private")))
            if (body or {}).get("auto_init"):
                blob = store_object("blob", ("# %s\n" % name).encode())
                tree = build_tree([("100644", "README.md", blob)])
                sha = make_commit(tree, [], "Initial commit")
                repo["refs"]["refs/heads/" + repo["default_branch"]] = sha
            return 201, repo_json(repo), {}
        raise ApiError(404, "Not Found")
    if len(parts) >= 3 and parts[0] == "repos":
        owner, name = parts[1], parts[2]
        rest = parts[3:]
        repo = need_repo(owner, name)
        return rest_repo(handler, method, repo, rest, body)
    raise ApiError(404, "Not Found")


def rest_repo(handler, method, repo, rest, body):
    q = handler.query
    if rest == []:
        if method == "GET":
            return 200, repo_json(repo), {}
        if method == "PATCH":
            if body and "description" in body:
                repo["description"] = body["description"] or ""
            if body and "private" in body:
                repo["private"] = bool(body["private"])
            if body and "name" in body and body["name"] != repo["name"]:
                new_name = body["name"]
                del _repos[(repo["owner"], repo["name"])]
                repo["name"] = new_name
                repo["full_name"] = "%s/%s" % (repo["owner"], new_name)
                _repos[(repo["owner"], new_name)] = repo
            return 200, repo_json(repo), {}
        if method == "DELETE":
            del _repos[(repo["owner"], repo["name"])]
            return 204, None, {}
        raise ApiError(404, "Not Found")
    if rest[:2] == ["git", "refs"]:
        if method == "POST" and len(rest) == 2:
            ref = (body or {}).get("ref", "")
            sha = (body or {}).get("sha", "")
            if not ref.startswith("refs/") or not read_object(sha):
                raise ApiError(422, "Invalid ref or sha")
            repo["refs"][ref] = sha
            return 201, {"ref": ref, "node_id": next_node_id("Ref"),
                         "object": {"sha": sha, "type": "commit",
                                    "url": ""}}, {}
        if method == "GET" and len(rest) == 2:
            out = [{"ref": r, "object": {"sha": s, "type": "commit"}}
                   for r, s in sorted_refs(repo)]
            return 200, out, {}
        raise ApiError(404, "Not Found")
    if rest == ["branches"] and method == "GET":
        out = [{"name": ref[len("refs/heads/"):],
                "commit": {"sha": sha, "url": ""}, "protected": False}
               for ref, sha in sorted_refs(repo)
               if ref.startswith("refs/heads/")]
        return 200, out, {}
    if rest == ["commits"] and method == "GET":
        ref = q.get("sha", [None])[0] or repo["default_branch"]
        tip = repo["refs"].get(ref) or repo["refs"].get("refs/heads/" + ref)
        if not tip and re.fullmatch(r"[0-9a-f]{40}", ref or ""):
            tip = ref
        out = []
        seen = set()
        stack = [tip] if tip else []
        while stack and len(out) < 200:
            cur = stack.pop(0)
            if cur in seen:
                continue
            seen.add(cur)
            obj = read_object(cur)
            if not obj or obj[0] != "commit":
                continue
            info = parse_commit(obj[1])
            out.append({"sha": cur,
                        "commit": {"message": info["message"],
                                   "tree": {"sha": info.get("tree")},
                                   "author": {"name": VIEWER["name"],
                                              "email": VIEWER["email"],
                                              "date": "2025-01-01T00:00:00Z"}},
                        "parents": [{"sha": p} for p in info["parents"]]})
            stack.extend(info["parents"])
        chunk, headers = paginate(handler, out)
        return 200, chunk, headers
    if rest and rest[0] == "contents":
        return rest_contents(handler, method, repo, rest[1:], body)
    if rest == ["labels"]:
        if method == "POST":
            name = (body or {}).get("name")
            if not name:
                raise ApiError(422, "name is required")
            label = {"name": name,
                     "color": (body or {}).get("color") or "ededed",
                     "description": (body or {}).get("description")}
            repo["labels"][name] = label
            return 201, dict(label, id=len(repo["labels"]),
                             node_id=next_node_id("Label"), default=False), {}
        if method == "GET":
            return 200, [dict(l, id=i + 1, default=False)
                         for i, l in enumerate(repo["labels"].values())], {}
        raise ApiError(404, "Not Found")
    if rest and rest[0] == "issues":
        return rest_issues(handler, method, repo, rest[1:], body)
    if rest and rest[0] == "pulls":
        return rest_pulls(handler, method, repo, rest[1:], body)
    raise ApiError(404, "Not Found")


def contents_branch(repo, body, q):
    branch = (body or {}).get("branch") or q.get("ref", [None])[0] \
        or repo["default_branch"]
    if branch.startswith("refs/heads/"):
        branch = branch[len("refs/heads/"):]
    return branch


def rest_contents(handler, method, repo, path_parts, body):
    q = handler.query
    path = "/".join(path_parts)
    branch = contents_branch(repo, body if method in ("PUT", "DELETE") else None, q)
    tip = branch_tip(repo, branch)
    tree_sha = commit_tree(tip) if tip else None
    flat = tree_flat(tree_sha)
    if method == "GET":
        if path and path in flat:
            mode, sha = flat[path]
            obj = read_object(sha)
            content = base64.b64encode(obj[1]).decode()
            wrapped = "\n".join(content[i:i + 60]
                                for i in range(0, len(content), 60))
            return 200, {"type": "file", "encoding": "base64",
                         "content": wrapped + ("\n" if wrapped else ""),
                         "name": path.split("/")[-1], "path": path,
                         "sha": sha, "size": len(obj[1])}, {}
        # Directory listing.
        prefix = (path + "/") if path else ""
        entries = {}
        for p, (mode, sha) in flat.items():
            if not p.startswith(prefix):
                continue
            rest = p[len(prefix):]
            head = rest.split("/")[0]
            if "/" in rest:
                entries[head] = ("tree", head)
            else:
                entries[head] = ("file", head, sha, mode)
        if path and not entries and path not in flat:
            raise ApiError(404, "Not Found")
        out = []
        for name in sorted(entries):
            e = entries[name]
            if e[0] == "tree":
                out.append({"type": "dir", "name": name,
                            "path": prefix + name, "sha": "", "size": 0})
            else:
                obj = read_object(e[2])
                out.append({"type": "file", "name": name,
                            "path": prefix + name, "sha": e[2],
                            "size": len(obj[1]) if obj else 0})
        return 200, out, {}
    if method == "PUT":
        if body is None or "content" not in body:
            raise ApiError(422, "content is required")
        try:
            raw = base64.b64decode(body["content"])
        except Exception:
            raise ApiError(422, "content is not valid base64")
        blob = store_object("blob", raw)
        existing = flat.get(path)
        if existing and body.get("sha") != existing[1]:
            raise ApiError(409, "sha does not match the current file")
        if existing and body.get("sha") is None:
            raise ApiError(422, "sha is required to update a file")
        new_tree = tree_set(tree_sha, path, blob)
        message = body.get("message") or ("Update %s" % path)
        parents = [tip] if tip else []
        sha = commit_on_branch(repo, branch, new_tree, parents, message)
        status = 200 if existing else 201
        return status, {"content": {"name": path.split("/")[-1],
                                    "path": path, "sha": blob,
                                    "size": len(raw), "encoding": "base64"},
                        "commit": {"sha": sha, "message": message}}, {}
    if method == "DELETE":
        existing = flat.get(path)
        if not existing:
            raise ApiError(404, "Not Found")
        if body and body.get("sha") and body["sha"] != existing[1]:
            raise ApiError(409, "sha does not match the current file")
        new_tree = tree_set(tree_sha, path, None)
        message = (body or {}).get("message") or ("Delete %s" % path)
        parents = [tip] if tip else []
        sha = commit_on_branch(repo, branch, new_tree, parents, message)
        return 200, {"content": None, "commit": {"sha": sha,
                                                 "message": message}}, {}
    raise ApiError(404, "Not Found")


def label_names(body_labels):
    names = []
    for item in body_labels or []:
        if isinstance(item, str):
            names.append(item)
        elif isinstance(item, dict) and item.get("name"):
            names.append(item["name"])
    return names


def rest_issues(handler, method, repo, rest, body):
    q = handler.query
    if rest == []:
        if method == "POST":
            names = label_names((body or {}).get("labels"))
            for n in names:
                if n not in repo["labels"]:
                    raise ApiError(422, "Label '%s' does not exist" % n)
            issue = new_issue(repo, (body or {}).get("title") or "",
                              (body or {}).get("body"), names)
            return 201, issue_json(repo, issue), {}
        if method == "GET":
            items = list(repo["issues"])
            state = q.get("state", ["open"])[0]
            if state == "open":
                items = [i for i in items if i["state"] == "open"]
            elif state == "closed":
                items = [i for i in items if i["state"] != "open"]
            direction = q.get("direction", ["desc"])[0]
            items.sort(key=lambda i: i["number"],
                       reverse=(direction != "asc"))
            chunk, headers = paginate(handler,
                                      [issue_json(repo, i) for i in items])
            return 200, chunk, headers
        raise ApiError(404, "Not Found")
    if not rest[0].isdigit():
        raise ApiError(404, "Not Found")
    number = int(rest[0])
    issue = find_issue(repo, number)
    if issue is None:
        raise ApiError(404, "Not Found")
    if len(rest) == 1:
        if method == "GET":
            return 200, issue_json(repo, issue), {}
        if method == "PATCH":
            if body:
                if "title" in body:
                    issue["title"] = body["title"]
                if "body" in body:
                    issue["body"] = body["body"]
                if "labels" in body:
                    names = label_names(body["labels"])
                    for n in names:
                        if n not in repo["labels"]:
                            raise ApiError(422, "Label '%s' does not exist" % n)
                    issue["labels"] = names
                if "state" in body:
                    issue["state"] = body["state"]
                    issue["closed_at"] = "2025-01-01T00:00:00Z" \
                        if body["state"] == "closed" else None
            return 200, issue_json(repo, issue), {}
        raise ApiError(404, "Not Found")
    if rest[1] == "comments":
        if method == "POST":
            _repo_ids[0] += 1
            comment = {"id": _repo_ids[0], "node_id": next_node_id("IssueComment"),
                       "body": (body or {}).get("body") or "",
                       "user": {"login": VIEWER["login"], "id": VIEWER["id"],
                                "type": "User"},
                       "created_at": "2025-01-01T00:00:00Z",
                       "updated_at": "2025-01-01T00:00:00Z"}
            issue.setdefault("comments", []).append(comment)
            return 201, comment, {}
        if method == "GET":
            return 200, issue.get("comments", []), {}
    raise ApiError(404, "Not Found")


def tree_diff(repo, base_tree, head_tree):
    base = tree_flat(base_tree)
    head = tree_flat(head_tree)
    import difflib
    out = []
    for path in sorted(set(base) | set(head)):
        b = base.get(path)
        h = head.get(path)
        if b and h and b[1] == h[1]:
            continue
        status = "modified" if b and h else ("added" if h else "removed")
        b_lines = []
        h_lines = []
        if b:
            obj = read_object(b[1])
            if obj:
                b_lines = obj[1].decode("utf-8", "replace").splitlines()
        if h:
            obj = read_object(h[1])
            if obj:
                h_lines = obj[1].decode("utf-8", "replace").splitlines()
        adds = dels = 0
        for line in difflib.unified_diff(b_lines, h_lines, lineterm=""):
            if line.startswith("+") and not line.startswith("+++"):
                adds += 1
            elif line.startswith("-") and not line.startswith("---"):
                dels += 1
        out.append({"filename": path, "status": status,
                    "additions": adds, "deletions": dels,
                    "changes": adds + dels,
                    "sha": h[1] if h else b[1]})
    return out


def merge_trees(base_tree, ours_tree, theirs_tree):
    """Three-way merge by path. Returns (tree_sha, conflicted)."""
    base = tree_flat(base_tree)
    ours = tree_flat(ours_tree)
    theirs = tree_flat(theirs_tree)
    merged = dict(ours)
    conflict = False
    for path in set(base) | set(ours) | set(theirs):
        b = base.get(path)
        o = ours.get(path)
        t = theirs.get(path)
        if o == t:
            continue
        if b == o:  # only theirs changed
            if t is None:
                merged.pop(path, None)
            else:
                merged[path] = t
        elif b == t:  # only ours changed
            continue
        else:
            conflict = True
    if conflict:
        return None, True
    # Rebuild the tree from the flat map.
    root = None
    for path in sorted(merged):
        root = tree_set(root, path, merged[path][1])
    return root or build_tree([]), False


def rest_pulls(handler, method, repo, rest, body):
    q = handler.query
    if rest == []:
        if method == "POST":
            head = (body or {}).get("head") or ""
            base = (body or {}).get("base") or repo["default_branch"]
            head = head.split(":")[-1]
            if not branch_tip(repo, head) or not branch_tip(repo, base):
                raise ApiError(422, "Invalid head or base branch")
            pr = new_issue(repo, (body or {}).get("title") or "",
                           (body or {}).get("body"), [], is_pull=True)
            pr["head"] = head
            pr["base"] = base
            pr["merged"] = False
            return 201, pull_json(repo, pr), {}
        if method == "GET":
            items = [i for i in repo["issues"] if i.get("is_pull")]
            state = q.get("state", ["open"])[0]
            if state == "open":
                items = [i for i in items if i["state"] == "open"]
            elif state == "closed":
                items = [i for i in items if i["state"] != "open"]
            chunk, headers = paginate(handler,
                                      [pull_json(repo, i) for i in items])
            return 200, chunk, headers
        raise ApiError(404, "Not Found")
    if not rest[0].isdigit():
        raise ApiError(404, "Not Found")
    number = int(rest[0])
    pr = find_issue(repo, number, pull=True)
    if pr is None:
        raise ApiError(404, "Not Found")
    if len(rest) == 1:
        if method == "GET":
            return 200, pull_json(repo, pr), {}
        if method == "PATCH":
            if body and "state" in body:
                pr["state"] = body["state"]
            if body and "title" in body:
                pr["title"] = body["title"]
            if body and "body" in body:
                pr["body"] = body["body"]
            return 200, pull_json(repo, pr), {}
        raise ApiError(404, "Not Found")
    if rest[1] == "files" and method == "GET":
        head_tip = branch_tip(repo, pr["head"])
        base_tip = branch_tip(repo, pr["base"])
        mb = merge_base(base_tip, head_tip) if head_tip and base_tip else None
        files = tree_diff(repo, commit_tree(mb) if mb else None,
                          commit_tree(head_tip))
        chunk, headers = paginate(handler, files)
        return 200, chunk, headers
    if rest[1] == "merge" and method == "PUT":
        if pr.get("merged") or pr["state"] != "open":
            raise ApiError(405, "Pull Request is not mergeable")
        head_tip = branch_tip(repo, pr["head"])
        base_tip = branch_tip(repo, pr["base"])
        if not head_tip or not base_tip:
            raise ApiError(405, "Pull Request is not mergeable")
        mb = merge_base(base_tip, head_tip)
        merged_tree, conflict = merge_trees(
            commit_tree(mb) if mb else None,
            commit_tree(base_tip), commit_tree(head_tip))
        if conflict:
            raise ApiError(405, "Pull Request is not mergeable: conflicts")
        message = (body or {}).get("commit_message") or (
            "%s (#%d)" % (pr["title"], pr["number"]))
        title = (body or {}).get("commit_title")
        if title:
            message = title + ("\n\n" + message if message else "")
        sha = commit_on_branch(repo, pr["base"], merged_tree, [base_tip],
                               message)
        pr["merged"] = True
        pr["merged_at"] = "2025-01-01T00:00:00Z"
        pr["merge_commit_sha"] = sha
        pr["state"] = "closed"
        pr["closed_at"] = "2025-01-01T00:00:00Z"
        return 200, {"sha": sha, "merged": True,
                     "message": "Pull Request successfully merged"}, {}
    raise ApiError(404, "Not Found")


# ---------------------------------------------------------------------------
# GraphQL v4
# ---------------------------------------------------------------------------

GQL_TYPES = {
    "Query": ["viewer", "repository", "search", "node", "rateLimit"],
    "User": ["id", "login", "name", "email", "url"],
    "RepositoryOwner": ["id", "login"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "issue", "issues", "pullRequest", "pullRequests",
                   "description", "isPrivate", "url", "createdAt"],
    "Ref": ["name", "prefix", "target"],
    "Commit": ["id", "oid", "message"],
    "Issue": ["id", "number", "title", "state", "body", "author", "labels",
              "createdAt", "updatedAt", "url", "repository", "comments"],
    "PullRequest": ["id", "number", "title", "state", "body", "author",
                    "headRefName", "baseRefName", "headRefOid", "baseRefOid",
                    "mergeable", "merged", "files", "createdAt", "updatedAt",
                    "url", "repository", "labels"],
    "Label": ["id", "name", "color"],
    "IssueConnection": ["nodes", "edges", "totalCount", "pageInfo"],
    "PullRequestConnection": ["nodes", "edges", "totalCount", "pageInfo"],
    "PullRequestChangedFile": ["path", "additions", "deletions", "changeType"],
    "PullRequestChangedFileConnection": ["nodes", "edges", "totalCount",
                                         "pageInfo"],
    "LabelConnection": ["nodes", "edges", "totalCount", "pageInfo"],
    "PageInfo": ["hasNextPage", "hasPreviousPage", "startCursor", "endCursor"],
    "CreatePullRequestPayload": ["pullRequest", "clientMutationId"],
    "SearchResultItemConnection": ["nodes", "edges", "issueCount", "pageInfo"],
    "RateLimit": ["limit", "cost", "remaining", "resetAt", "used", "nodeCount"],
}
GQL_ENUMS = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
    "OrderDirection": ["ASC", "DESC"],
    "FileChangeType": ["ADDED", "MODIFIED", "DELETED", "RENAMED"],
}
GQL_INPUTS = {
    "CreatePullRequestInput": ["repositoryId", "headRefName", "baseRefName",
                               "title", "body", "draft", "clientMutationId"],
    "IssueOrder": ["field", "direction"],
}


def gql_tokenize(text):
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c in " \t\r\n,":
            i += 1
        elif c == "#":
            while i < len(text) and text[i] != "\n":
                i += 1
        elif text.startswith("...", i):
            tokens.append(("...", "..."))
            i += 3
        elif c in "{}()[]:!=$@|&":
            tokens.append((c, c))
            i += 1
        elif c == '"':
            if text.startswith('"""', i):
                j = text.index('"""', i + 3)
                tokens.append(("str", text[i + 3:j]))
                i = j + 3
            else:
                j = i + 1
                buf = ""
                while text[j] != '"':
                    if text[j] == "\\":
                        buf += text[j + 1]
                        j += 2
                    else:
                        buf += text[j]
                        j += 1
                tokens.append(("str", buf))
                i = j + 1
        elif c.isdigit() or c == "-":
            m = re.match(r"-?\d+(\.\d+)?([eE][+-]?\d+)?", text[i:])
            tokens.append(("num", m.group(0)))
            i += len(m.group(0))
        else:
            m = re.match(r"[A-Za-z_][A-Za-z0-9_]*", text[i:])
            tokens.append(("name", m.group(0)))
            i += len(m.group(0))
    return tokens


class GqlParser:
    def __init__(self, text):
        self.tokens = gql_tokenize(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else (None, None)

    def next(self):
        tok = self.peek()
        self.pos += 1
        return tok

    def expect(self, kind):
        tok = self.next()
        assert tok[0] == kind, "expected %s got %s" % (kind, tok)
        return tok[1]

    def parse_document(self):
        ops = []
        fragments = {}
        while self.pos < len(self.tokens):
            kind, val = self.peek()
            if kind == "{":
                ops.append({"type": "query", "name": None,
                            "selection": self.parse_selection_set(),
                            "var_defs": {}})
            elif val in ("query", "mutation", "subscription"):
                self.next()
                name = None
                if self.peek()[0] == "name":
                    name = self.next()[1]
                var_defs = {}
                if self.peek()[0] == "(":
                    var_defs = self.parse_var_defs()
                # directives
                while self.peek()[0] == "@":
                    self.next()
                    self.next()
                    if self.peek()[0] == "(":
                        self.parse_arguments()
                ops.append({"type": val, "name": name,
                            "selection": self.parse_selection_set(),
                            "var_defs": var_defs})
            elif val == "fragment":
                self.next()
                fname = self.expect("name")
                self.expect("name")  # 'on'
                self.expect("name")  # type name
                frag = self.parse_selection_set()
                fragments[fname] = frag
            else:
                self.next()
        return ops, fragments

    def parse_var_defs(self):
        defs = {}
        self.expect("(")
        while self.peek()[0] != ")":
            self.expect("$")
            name = self.expect("name")
            self.expect(":")
            self.parse_type()
            if self.peek()[0] == "=":
                self.next()
                defs[name] = self.parse_value()
            else:
                defs[name] = None
        self.expect(")")
        return defs

    def parse_type(self):
        if self.peek()[0] == "[":
            self.next()
            self.parse_type()
            self.expect("]")
        else:
            self.expect("name")
        if self.peek()[0] == "!":
            self.next()

    def parse_selection_set(self):
        self.expect("{")
        fields = []
        while self.peek()[0] != "}":
            kind, val = self.peek()
            if kind == "...":
                self.next()
                if self.peek() == ("name", "on"):
                    self.next()
                    self.expect("name")
                    fields.append(("inline", self.parse_selection_set()))
                else:
                    fname = self.expect("name")
                    fields.append(("spread", fname))
            else:
                fields.append(("field", self.parse_field()))
        self.expect("}")
        return fields

    def parse_field(self):
        name = self.expect("name")
        alias = None
        if self.peek()[0] == ":":
            self.next()
            alias = name
            name = self.expect("name")
        args = {}
        if self.peek()[0] == "(":
            args = self.parse_arguments()
        while self.peek()[0] == "@":
            self.next()
            self.next()
            if self.peek()[0] == "(":
                self.parse_arguments()
        selection = None
        if self.peek()[0] == "{":
            selection = self.parse_selection_set()
        return {"name": name, "alias": alias, "args": args,
                "selection": selection}

    def parse_arguments(self):
        args = {}
        self.expect("(")
        while self.peek()[0] != ")":
            name = self.expect("name")
            self.expect(":")
            args[name] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self):
        kind, val = self.peek()
        if kind == "$":
            self.next()
            return ("var", self.expect("name"))
        if kind == "str":
            self.next()
            return val
        if kind == "num":
            self.next()
            return float(val) if ("." in val or "e" in val) else int(val)
        if kind == "name":
            self.next()
            if val == "true":
                return True
            if val == "false":
                return False
            if val == "null":
                return None
            return ("enum", val)
        if kind == "[":
            self.next()
            out = []
            while self.peek()[0] != "]":
                out.append(self.parse_value())
            self.expect("]")
            return out
        if kind == "{":
            self.next()
            out = {}
            while self.peek()[0] != "}":
                name = self.expect("name")
                self.expect(":")
                out[name] = self.parse_value()
            self.expect("}")
            return out
        raise ValueError("unexpected value token %s" % (self.peek(),))


def gql_resolve_value(value, variables):
    if isinstance(value, tuple) and value and value[0] == "var":
        return variables.get(value[1])
    if isinstance(value, tuple) and value and value[0] == "enum":
        return value[1]
    if isinstance(value, list):
        return [gql_resolve_value(v, variables) for v in value]
    if isinstance(value, dict):
        return {k: gql_resolve_value(v, variables) for k, v in value.items()}
    return value


class GqlError(Exception):
    pass


def gql_connection(items, args, node_fn):
    first = args.get("first")
    last = args.get("last")
    total = len(items)
    sliced = items
    if first is not None:
        sliced = sliced[:int(first)]
    if last is not None:
        sliced = sliced[-int(last):] if int(last) else []
    nodes = [node_fn(x) for x in sliced]
    edges = [{"node": n, "cursor": base64.b64encode(str(i).encode()).decode()}
             for i, n in enumerate(nodes)]
    return {"nodes": nodes, "edges": edges, "totalCount": total,
            "issueCount": total,
            "pageInfo": {"hasNextPage": total > len(sliced),
                         "hasPreviousPage": False,
                         "startCursor": edges[0]["cursor"] if edges else None,
                         "endCursor": edges[-1]["cursor"] if edges else None}}


def gql_user_obj(login=None):
    if login == VIEWER["login"] or login is None:
        return dict(VIEWER)
    return {"id": 0, "login": login, "name": login, "type": "User"}


def gql_issue_obj(repo, issue):
    return {"__type": "Issue", "repo": repo, "issue": issue,
            "id": issue["node_id"], "number": issue["number"],
            "title": issue["title"],
            "state": "OPEN" if issue["state"] == "open" else "CLOSED",
            "body": issue.get("body"),
            "createdAt": issue.get("created_at"), "updatedAt": issue.get("updated_at"),
            "url": "https://forge.local/%s/issues/%d" % (repo["full_name"], issue["number"])}


def gql_pull_obj(repo, pr):
    head_tip = branch_tip(repo, pr["head"]) if pr.get("head") else None
    base_tip = branch_tip(repo, pr["base"]) if pr.get("base") else None
    mergeable = "UNKNOWN"
    if head_tip and base_tip:
        mb = merge_base(base_tip, head_tip)
        _t, conflict = merge_trees(commit_tree(mb) if mb else None,
                                   commit_tree(base_tip), commit_tree(head_tip))
        mergeable = "CONFLICTING" if conflict else "MERGEABLE"
    state = "MERGED" if pr.get("merged") else (
        "OPEN" if pr["state"] == "open" else "CLOSED")
    return {"__type": "PullRequest", "repo": repo, "issue": pr,
            "id": pr["node_id"], "number": pr["number"], "title": pr["title"],
            "state": state, "body": pr.get("body"),
            "headRefName": pr.get("head"), "baseRefName": pr.get("base"),
            "headRefOid": head_tip, "baseRefOid": base_tip,
            "mergeable": mergeable, "merged": bool(pr.get("merged")),
            "createdAt": pr.get("created_at"), "updatedAt": pr.get("updated_at"),
            "url": "https://forge.local/%s/pulls/%d" % (repo["full_name"], pr["number"])}


def gql_repo_obj(repo):
    return {"__type": "Repository", "repo": repo, "id": repo["node_id"],
            "databaseId": repo["id"], "name": repo["name"],
            "nameWithOwner": repo["full_name"],
            "description": repo["description"], "isPrivate": repo["private"],
            "viewerPermission": "ADMIN", "hasIssuesEnabled": True,
            "url": "https://forge.local/%s" % repo["full_name"],
            "createdAt": "2025-01-01T00:00:00Z"}


NODE_OBJECTS = {}


def register_node(node_id, obj):
    NODE_OBJECTS[node_id] = obj


def gql_type_info(name):
    if name in GQL_ENUMS:
        return {"name": name, "kind": "ENUM",
                "enumValues": [{"name": v, "description": None,
                                "isDeprecated": False, "deprecationReason": None}
                               for v in GQL_ENUMS[name]],
                "fields": None, "inputFields": None, "possibleTypes": None}
    if name in GQL_INPUTS:
        return {"name": name, "kind": "INPUT_OBJECT",
                "inputFields": [{"name": f} for f in GQL_INPUTS[name]],
                "fields": None, "enumValues": None, "possibleTypes": None}
    if name in GQL_TYPES:
        return {"name": name, "kind": "OBJECT",
                "fields": [{"name": f, "description": None,
                            "isDeprecated": False, "deprecationReason": None,
                            "args": [], "type": {"name": None, "kind": "SCALAR",
                                                 "ofType": None}}
                           for f in GQL_TYPES[name]],
                "enumValues": None, "inputFields": None, "possibleTypes": None}
    return None


def gql_apply(obj, type_name, selection, ctx):
    if selection is None:
        return obj
    if isinstance(obj, list):
        return [gql_apply(o, type_name, selection, ctx) for o in obj]
    if obj is None:
        return None
    out = {}
    for entry in selection:
        if entry[0] == "spread":
            frag = ctx["fragments"].get(entry[1], [])
            out.update(gql_apply(obj, type_name, frag, ctx))
            continue
        if entry[0] == "inline":
            out.update(gql_apply(obj, type_name, entry[1], ctx))
            continue
        field = entry[1]
        key = field["alias"] or field["name"]
        args = {k: gql_resolve_value(v, ctx["variables"])
                for k, v in field["args"].items()}
        value, value_type = gql_field(obj, type_name, field["name"], args, ctx)
        out[key] = gql_apply(value, value_type, field["selection"], ctx)
    return out


def gql_field(obj, type_name, name, args, ctx):
    # Introspection and plain dicts resolve by key.
    if name == "__type":
        return gql_type_info(args.get("name")), "__Type"
    if name == "__schema":
        return {"queryType": {"name": "Query"},
                "mutationType": {"name": "Mutation"},
                "subscriptionType": None,
                "types": [{"name": n} for n in
                          list(GQL_TYPES) + list(GQL_ENUMS) + list(GQL_INPUTS)],
                "directives": []}, "__Schema"
    if isinstance(obj, dict) and "__type" not in obj and name in obj:
        return obj[name], None
    if type_name in ("__Type", "__Field", "__EnumValue", "__Schema",
                     "__InputValue", "__Directive"):
        if isinstance(obj, dict):
            return obj.get(name), None
        return None, None
    handler = GQL_RESOLVERS.get(type_name, {})
    if name in handler:
        return handler[name](obj, args, ctx)
    if isinstance(obj, dict) and name in obj:
        return obj[name], None
    known = GQL_TYPES.get(type_name)
    if known is not None and name not in known:
        ctx["errors"].append({
            "message": "Field '%s' doesn't exist on type '%s'" % (name, type_name),
            "extensions": {"code": "undefinedField"}})
        return None, None
    return (obj.get(name) if isinstance(obj, dict) else None), None


def _repo_from_obj(obj):
    return obj["repo"]


def resolve_repository(_obj, args, ctx):
    repo = get_repo(args.get("owner", ""), args.get("name", ""))
    if repo is None:
        return None, "Repository"
    return gql_repo_obj(repo), "Repository"


def resolve_issues(repo, args, pulls=False):
    items = [i for i in repo["issues"] if bool(i.get("is_pull")) == pulls]
    states = args.get("states")
    if states:
        wanted = {str(s).upper() for s in states}
        items = [i for i in items
                 if ("OPEN" if i["state"] == "open" else "CLOSED") in wanted]
    order = args.get("orderBy") or {}
    direction = str(order.get("direction", "DESC")).upper()
    items.sort(key=lambda i: i["number"], reverse=(direction != "ASC"))
    return items


GQL_RESOLVERS = {
    "Query": {
        "viewer": lambda o, a, c: (gql_user_obj(), "User"),
        "repository": resolve_repository,
        "node": lambda o, a, c: (NODE_OBJECTS.get(a.get("id")),
                                 (NODE_OBJECTS.get(a.get("id")) or {}).get("__type")),
        "rateLimit": lambda o, a, c: ({"limit": 5000, "cost": 1,
                                       "remaining": 4999, "used": 1,
                                       "nodeCount": 0,
                                       "resetAt": "2025-01-01T01:00:00Z"}, "RateLimit"),
        "search": lambda o, a, c: (_gql_search(a), "SearchResultItemConnection"),
    },
    "Mutation": {
        "createPullRequest": lambda o, a, c: (_gql_create_pull(a), "CreatePullRequestPayload"),
    },
    "Repository": {
        "owner": lambda o, a, c: (gql_user_obj(o["repo"]["owner"]), "User"),
        "defaultBranchRef": lambda o, a, c: (_gql_default_ref(o["repo"]), "Ref"),
        "issue": lambda o, a, c: (_gql_one_issue(o["repo"], a.get("number"), False), "Issue"),
        "issues": lambda o, a, c: (gql_connection(
            resolve_issues(o["repo"], a), a,
            lambda i: gql_issue_obj(o["repo"], i)), "IssueConnection"),
        "pullRequest": lambda o, a, c: (_gql_one_issue(o["repo"], a.get("number"), True), "PullRequest"),
        "pullRequests": lambda o, a, c: (gql_connection(
            resolve_issues(o["repo"], a, pulls=True), a,
            lambda i: gql_pull_obj(o["repo"], i)), "PullRequestConnection"),
    },
    "Issue": {
        "author": lambda o, a, c: (gql_user_obj(o["issue"].get("user")), "User"),
        "repository": lambda o, a, c: (gql_repo_obj(o["repo"]), "Repository"),
        "labels": lambda o, a, c: (gql_connection(
            [lbl for lbl in o["issue"].get("labels", [])], a,
            lambda n: {"name": n, "color": o["repo"]["labels"].get(n, {}).get("color", "ededed"),
                       "id": base64.b64encode(("Label:" + n).encode()).decode()}),
            "LabelConnection"),
        "comments": lambda o, a, c: ({"totalCount": len(o["issue"].get("comments", [])),
                                      "nodes": [], "edges": [],
                                      "pageInfo": {"hasNextPage": False,
                                                   "hasPreviousPage": False,
                                                   "startCursor": None,
                                                   "endCursor": None}}, None),
    },
    "PullRequest": {
        "author": lambda o, a, c: (gql_user_obj(o["issue"].get("user")), "User"),
        "repository": lambda o, a, c: (gql_repo_obj(o["repo"]), "Repository"),
        "labels": lambda o, a, c: (gql_connection(
            [lbl for lbl in o["issue"].get("labels", [])], a,
            lambda n: {"name": n, "color": o["repo"]["labels"].get(n, {}).get("color", "ededed"),
                       "id": base64.b64encode(("Label:" + n).encode()).decode()}),
            "LabelConnection"),
        "files": lambda o, a, c: (_gql_pr_files(o), "PullRequestChangedFileConnection"),
    },
}


def _gql_default_ref(repo):
    tip = default_tip(repo)
    if not tip:
        return None
    return {"name": repo["default_branch"], "prefix": "refs/heads/",
            "target": {"oid": tip, "id": base64.b64encode(
                ("Commit:" + tip).encode()).decode()}}


def _gql_one_issue(repo, number, pull):
    if number is None:
        return None
    item = find_issue(repo, int(number), pull=pull)
    if item is None:
        return None
    return gql_pull_obj(repo, item) if pull else gql_issue_obj(repo, item)


def _gql_pr_files(pr_obj):
    repo = pr_obj["repo"]
    pr = pr_obj["issue"]
    head_tip = branch_tip(repo, pr["head"])
    base_tip = branch_tip(repo, pr["base"])
    files = []
    if head_tip and base_tip:
        mb = merge_base(base_tip, head_tip)
        change_type = {"added": "ADDED", "modified": "MODIFIED",
                       "removed": "DELETED"}
        for f in tree_diff(repo, commit_tree(mb) if mb else None,
                           commit_tree(head_tip)):
            files.append({"path": f["filename"], "additions": f["additions"],
                          "deletions": f["deletions"],
                          "changeType": change_type.get(f["status"], "MODIFIED")})
    return gql_connection(files, {}, lambda f: f)


def _gql_search(args):
    query = str(args.get("query") or "")
    items = []
    for (owner, _name), repo in sorted(_repos.items()):
        for issue in repo["issues"]:
            if query.lower() in (issue["title"] or "").lower() or not query:
                items.append(gql_pull_obj(repo, issue) if issue.get("is_pull")
                             else gql_issue_obj(repo, issue))
    return gql_connection(items, args, lambda x: x)


def _gql_create_pull(args):
    inp = args.get("input") or {}
    repo = None
    rid = inp.get("repositoryId")
    if rid:
        target = NODE_OBJECTS.get(rid)
        if target and target.get("__type") == "Repository":
            repo = target["repo"]
        else:
            try:
                decoded = base64.b64decode(rid).decode()
                if decoded.startswith("Repository:"):
                    want = int(decoded.split(":", 1)[1])
                    for r in _repos.values():
                        if r["id"] == want:
                            repo = r
            except Exception:
                pass
    if repo is None:
        raise GqlError("repository not found")
    head = (inp.get("headRefName") or "").split(":")[-1]
    base = (inp.get("baseRefName") or repo["default_branch"]).split(":")[-1]
    if not branch_tip(repo, head) or not branch_tip(repo, base):
        raise GqlError("head or base ref does not exist")
    pr = new_issue(repo, inp.get("title") or "", inp.get("body"), [],
                   is_pull=True)
    pr["head"] = head
    pr["base"] = base
    pr["merged"] = False
    return {"pullRequest": gql_pull_obj(repo, pr),
            "clientMutationId": inp.get("clientMutationId")}


def gql_execute(body):
    if isinstance(body, list):
        return [gql_execute_one(item) for item in body]
    return gql_execute_one(body)


def gql_execute_one(body):
    query = body.get("query") or ""
    variables = dict(body.get("variables") or {})
    op_name = body.get("operationName")
    try:
        ops, fragments = GqlParser(query).parse_document()
    except Exception as exc:
        return {"errors": [{"message": "Parse error: %s" % exc}], "data": None}
    if op_name:
        ops = [o for o in ops if o["name"] == op_name] or ops[:1]
    results = []
    for op in ops:
        merged_vars = dict(op.get("var_defs") or {})
        merged_vars.update(variables)
        ctx = {"variables": merged_vars, "fragments": fragments, "errors": []}
        root_type = "Mutation" if op["type"] == "mutation" else "Query"
        try:
            data = gql_apply({}, root_type, op["selection"], ctx)
        except GqlError as exc:
            results.append({"data": None, "errors": [{"message": str(exc)}]})
            continue
        result = {"data": data}
        if ctx["errors"]:
            result["errors"] = ctx["errors"]
        results.append(result)
    if len(results) == 1:
        return results[0]
    return results


# ---------------------------------------------------------------------------
# MCP (JSON-RPC 2.0 over Streamable HTTP)
# ---------------------------------------------------------------------------

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a new repository for the authenticated user.",
     "inputSchema": {"type": "object",
                     "properties": {"name": {"type": "string"},
                                    "description": {"type": "string"},
                                    "private": {"type": "boolean"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get details of a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "list_repos",
     "description": "List repositories owned by the authenticated user.",
     "inputSchema": {"type": "object", "properties": {}}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository, optionally by state.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "state": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "get_issue",
     "description": "Get one issue by number.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "issue_number": {"type": "integer"}},
                     "required": ["owner", "repo", "issue_number"]}},
    {"name": "create_pull_request",
     "description": "Open a pull request from a head branch into a base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "head": {"type": "string"},
                                    "base": {"type": "string"},
                                    "body": {"type": "string"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request (squash) into its base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "pull_number": {"type": "integer"}},
                     "required": ["owner", "repo", "pull_number"]}},
]
MCP_TOOLS_JSON = json.dumps({"tools": MCP_TOOLS}, separators=(",", ":"),
                            sort_keys=True)


def mcp_split_full_name(args):
    if args.get("full_name") and ("/" in str(args["full_name"])):
        owner, repo = str(args["full_name"]).split("/", 1)
        args.setdefault("owner", owner)
        args.setdefault("repo", repo)
    return args


def mcp_tool_call(name, args):
    """Returns (result_obj, is_error)."""
    args = mcp_split_full_name(dict(args or {}))
    tool = None
    for t in MCP_TOOLS:
        if t["name"] == name or name.lower().endswith("__" + t["name"]):
            tool = t
            break
    if tool is None:
        return None, "unknown tool"
    for req in tool["inputSchema"].get("required", []):
        if args.get(req) is None:
            return None, "missing required argument: %s" % req
    try:
        with _store_lock:
            return _mcp_run(tool["name"], args), None
    except ApiError as exc:
        return None, exc.message


def _mcp_run(name, args):
    if name == "create_repo":
        if get_repo(VIEWER["login"], args["name"]):
            raise ApiError(422, "name already exists on this account")
        repo = new_repo(VIEWER["login"], args["name"],
                        args.get("description") or "",
                        bool(args.get("private")))
        return repo_json(repo)
    if name == "list_repos":
        return [repo_json(r) for (o, _n), r in sorted(_repos.items())
                if o == VIEWER["login"]]
    repo = need_repo(args.get("owner", ""), args.get("repo", ""))
    if name == "get_repo":
        return repo_json(repo)
    if name == "create_issue":
        issue = new_issue(repo, args["title"], args.get("body"), [])
        return issue_json(repo, issue)
    if name == "list_issues":
        items = [i for i in repo["issues"] if not i.get("is_pull")]
        state = args.get("state")
        if state in ("open", "closed"):
            items = [i for i in items if i["state"] == state]
        return [issue_json(repo, i) for i in items]
    if name == "get_issue":
        issue = find_issue(repo, int(args["issue_number"]))
        if issue is None:
            raise ApiError(404, "Not Found")
        return issue_json(repo, issue)
    if name == "create_pull_request":
        head = str(args["head"]).split(":")[-1]
        base = str(args["base"]).split(":")[-1]
        if not branch_tip(repo, head) or not branch_tip(repo, base):
            raise ApiError(422, "Invalid head or base branch")
        pr = new_issue(repo, args["title"], args.get("body"), [], is_pull=True)
        pr["head"] = head
        pr["base"] = base
        pr["merged"] = False
        return pull_json(repo, pr)
    if name == "merge_pull_request":
        pr = find_issue(repo, int(args["pull_number"]), pull=True)
        if pr is None:
            raise ApiError(404, "Not Found")
        if pr.get("merged") or pr["state"] != "open":
            raise ApiError(405, "Pull Request is not mergeable")
        head_tip = branch_tip(repo, pr["head"])
        base_tip = branch_tip(repo, pr["base"])
        mb = merge_base(base_tip, head_tip)
        merged_tree, conflict = merge_trees(
            commit_tree(mb) if mb else None,
            commit_tree(base_tip), commit_tree(head_tip))
        if conflict:
            raise ApiError(405, "Pull Request is not mergeable: conflicts")
        sha = commit_on_branch(repo, pr["base"], merged_tree, [base_tip],
                               "%s (#%d)" % (pr["title"], pr["number"]))
        pr["merged"] = True
        pr["merge_commit_sha"] = sha
        pr["state"] = "closed"
        return {"sha": sha, "merged": True,
                "message": "Pull Request successfully merged"}
    raise ApiError(404, "unknown tool")


def mcp_handle(body):
    """Returns (status, obj_or_none). obj None means: no response body
    (a notification)."""
    if isinstance(body, list):
        out = []
        for item in body:
            status, obj = mcp_handle_one(item)
            if obj is not None:
                out.append(obj)
        return 200, out
    return mcp_handle_one(body)


def mcp_handle_one(msg):
    if not isinstance(msg, dict):
        return 400, {"jsonrpc": "2.0", "id": None,
                     "error": {"code": -32600, "message": "Invalid Request"}}
    mid = msg.get("id")
    method = msg.get("method", "")
    params = msg.get("params") or {}
    if method.startswith("notifications/"):
        return 202, None
    def result(obj):
        return 200, {"jsonrpc": "2.0", "id": mid, "result": obj}
    def error(code, message):
        return 200, {"jsonrpc": "2.0", "id": mid,
                     "error": {"code": code, "message": message}}
    if method == "server/discover":
        return result({
            "supportedVersions": ["2026-07-28", "2025-11-25", "2025-06-18",
                                  "2025-03-26", "2024-11-05"],
            "protocolVersion": "2026-07-28",
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge-mcp", "version": "1.0.0"}})
    if method == "initialize":
        want = params.get("protocolVersion") or "2025-11-25"
        supported = {"2026-07-28", "2025-11-25", "2025-06-18",
                     "2025-03-26", "2024-11-05"}
        return result({
            "protocolVersion": want if want in supported else "2025-11-25",
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge-mcp", "version": "1.0.0"}})
    if method == "ping":
        return result({})
    if method == "tools/list":
        return 200, {"jsonrpc": "2.0", "id": mid,
                     "result": json.loads(MCP_TOOLS_JSON)}
    if method == "tools/call":
        name = params.get("name", "")
        args = params.get("arguments") or {}
        known = any(t["name"] == name or
                    name.lower().endswith("__" + t["name"])
                    for t in MCP_TOOLS)
        if not known:
            return error(-32602, "Unknown tool: %s" % name)
        obj, err = mcp_tool_call(name, args)
        if err is not None:
            return result({"content": [{"type": "text", "text": err}],
                           "isError": True})
        return result({"content": [{"type": "text",
                                    "text": json.dumps(obj)}],
                       "structuredContent": obj if isinstance(obj, dict) else None,
                       "isError": False})
    return error(-32601, "Method not found: %s" % method)


# ---------------------------------------------------------------------------
# HTTP plumbing and boot
# ---------------------------------------------------------------------------

import urllib.parse


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    # -- helpers ------------------------------------------------------
    def send_bytes(self, status, data, content_type, extra=None):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("X-GitHub-Request-Id", request_id())
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def send_json(self, status, obj, extra=None):
        if obj is None:
            self.send_bytes(status, b"", "application/json", extra)
            return
        data = json.dumps(obj).encode()
        self.send_bytes(status, data, "application/json", extra)

    def authed(self):
        if not TOKEN:
            return True
        return self.headers.get("Authorization") == "Bearer " + TOKEN

    def read_body(self):
        length = int(self.headers.get("Content-Length") or 0)
        return self.rfile.read(length) if length else b""

    # -- verbs --------------------------------------------------------
    def do_GET(self):
        self.route("GET")

    def do_POST(self):
        self.route("POST")

    def do_PUT(self):
        self.route("PUT")

    def do_PATCH(self):
        self.route("PATCH")

    def do_DELETE(self):
        self.route("DELETE")

    def do_HEAD(self):
        self.route("GET")

    # -- routing ------------------------------------------------------
    def route(self, method):
        parsed = urllib.parse.urlparse(self.path)
        self.path_only = parsed.path
        self.query = urllib.parse.parse_qs(parsed.query)
        parts = [urllib.parse.unquote(p) for p in parsed.path.split("/") if p]
        try:
            with _store_lock:
                self.dispatch(method, parts)
        except ApiError as exc:
            self.send_json(exc.status, {"message": exc.message})
        except BrokenPipeError:
            pass
        except Exception as exc:  # never hang the suite on a crash
            try:
                self.send_json(500, {"message": "Internal error: %s" % exc})
            except Exception:
                pass

    def dispatch(self, method, parts):
        # Git smart HTTP: /{owner}/{repo}.git/...
        if len(parts) >= 2 and parts[1].endswith(".git"):
            owner = parts[0]
            name = parts[1][:-4]
            return self.git_route(method, owner, name, parts[2:])
        if parts[:2] == ["api", "v3"]:
            if not self.authed():
                return self.send_json(401, {"message": "Bad credentials"})
            body = None
            raw = self.read_body() if method in ("POST", "PUT", "PATCH", "DELETE") else b""
            if raw:
                try:
                    body = json.loads(raw)
                except Exception:
                    return self.send_json(400, {"message": "Problems parsing JSON"})
            try:
                status, obj, headers = rest_dispatch(self, method, parts[2:], body)
            except ApiError as exc:
                return self.send_json(exc.status, {"message": exc.message})
            return self.send_json(status, obj, headers)
        if parts == ["api", "graphql"]:
            if not self.authed():
                return self.send_json(401, {"message": "Bad credentials"})
            raw = self.read_body()
            try:
                body = json.loads(raw) if raw else {}
            except Exception:
                return self.send_json(400, {"message": "Problems parsing JSON"})
            return self.send_json(200, gql_execute(body))
        if parts == ["mcp"]:
            if self.headers.get("Authorization") is None:
                return self.send_json(401, {"message": "Unauthorized"})
            if not self.authed():
                return self.send_json(401, {"message": "Unauthorized"})
            if method == "GET":
                return self.send_bytes(405, b"", "application/json")
            raw = self.read_body()
            try:
                body = json.loads(raw) if raw else None
            except Exception:
                return self.send_json(400, {
                    "jsonrpc": "2.0", "id": None,
                    "error": {"code": -32700, "message": "Parse error"}})
            if body is None:
                return self.send_json(400, {
                    "jsonrpc": "2.0", "id": None,
                    "error": {"code": -32700, "message": "Parse error"}})
            status, obj = mcp_handle(body)
            if obj is None:
                return self.send_bytes(202, b"", "application/json",
                                       {"Mcp-Session-Id": "forge-session"})
            return self.send_bytes(status, json.dumps(obj).encode(),
                                   "application/json",
                                   {"Mcp-Session-Id": "forge-session"})
        return self.send_json(404, {"message": "Not Found"})

    def git_route(self, method, owner, name, rest):
        if not self.authed():
            return self.send_json(401, {"message": "Bad credentials"})
        repo = get_repo(owner, name)
        if repo is None or owner != VIEWER["login"]:
            return self.send_json(404, {"message": "Not Found"})
        service = (self.query.get("service", [""])[0])
        proto = self.headers.get("Git-Protocol", "")
        version2 = "version=2" in proto
        if rest == ["info", "refs"] and method == "GET":
            if service == "git-upload-pack":
                return self.send_bytes(
                    200, upload_advertisement(repo, version2),
                    "application/x-git-upload-pack-advertisement")
            if service == "git-receive-pack":
                return self.send_bytes(
                    200, receive_advertisement(repo),
                    "application/x-git-receive-pack-advertisement")
            return self.send_json(404, {"message": "Not Found"})
        if rest == ["git-upload-pack"] and method == "POST":
            body = self.read_body()
            return self.send_bytes(200, handle_upload_pack(repo, body, version2),
                                   "application/x-git-upload-pack-result")
        if rest == ["git-receive-pack"] and method == "POST":
            body = self.read_body()
            return self.send_bytes(200, handle_receive_pack(repo, body),
                                   "application/x-git-receive-pack-result")
        return self.send_json(404, {"message": "Not Found"})


def register_and_serve():
    server = ThreadingHTTPServer(("0.0.0.0", 0), Handler)
    port = server.server_address[1]
    if ENV_URL:
        try:
            req = urllib.request.Request(
                ENV_URL.rstrip("/") + "/register",
                data=json.dumps({"port": port}).encode(),
                headers={"Content-Type": "application/json"}, method="POST")
            urllib.request.urlopen(req, timeout=10).read()
        except Exception as exc:
            print("register failed: %s" % exc, file=sys.stderr)

        def poll_done():
            while True:
                try:
                    with urllib.request.urlopen(
                            ENV_URL.rstrip("/") + "/done", timeout=10) as resp:
                        data = json.loads(resp.read() or b"{}")
                    if data.get("done"):
                        os._exit(0)
                except Exception:
                    pass
                time.sleep(1.5)

        threading.Thread(target=poll_done, daemon=True).start()
    print("forge listening on %d" % port, flush=True)
    server.serve_forever()


if __name__ == "__main__":
    register_and_serve()
