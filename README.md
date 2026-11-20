# Coreforge — a GitHub-compatible git forge in one Python file

A standalone forge that runs as a single process on Python's standard
library alone: no git binary, no packages, no network beyond the
client beside it.

## What it serves

One in-memory store of git objects (blobs, trees, commits, kept by
SHA-1) backs four surfaces, so state is shared across all of them — a
file written through the contents API is the blob a clone fetches, and
a branch pushed over git is the ref a pull request names:

- **Git smart HTTP** at `/{owner}/{repo}.git` — upload-pack protocol
  v2 (`ls-refs` with symrefs/peeling/unborn, `fetch` with have/want
  negotiation, shallow clones with boundary trees) with a protocol v0
  fallback, and receive-pack v0 with report-status, side-band-64k and
  delete-refs. Every update must fast-forward; a mixed push applies
  the fast-forward refs and refuses the rest per ref.
- **REST v3** under `/api/v3` — repositories, contents (create, update
  with sha checks, delete), git refs, branches, commits, labels,
  issues with comments, and pull requests with file diffs and squash
  merges (three-way by path, conflicts answer 405).
- **GraphQL v4** at `/api/graphql` — viewer, repository, issue and
  pull-request queries with connections and ordering, introspection
  for the types the GitHub clients send, and the `createPullRequest`
  mutation.
- **MCP** at `/mcp` — JSON-RPC 2.0 over Streamable HTTP: discovery,
  initialize, and tools (`create_repo`, `get_repo`, `list_repos`,
  `create_issue`, `list_issues`, `get_issue`, `create_pull_request`,
  `merge_pull_request`) acting on the same store as REST.

Authentication is a single bearer token; a repository belongs to the
login the token names, and the same name under another owner is a 404.

## Running

```
MAKEFUN_SHOP_TOKEN=<token> MAKEFUN_ENV_URL=<env> python3 main.py
```

The forge binds an ephemeral port, registers it with
`$MAKEFUN_ENV_URL/register`, and exits 0 when the environment's
`/done` long-poll answers done. With no `MAKEFUN_ENV_URL` it just
serves (handy for local testing with curl and a real git client).
