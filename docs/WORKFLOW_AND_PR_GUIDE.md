# Workflow and PR Guide

## Track-based parallelism

Work is decomposed into independent tracks, listed in [`TRACKS.md`](TRACKS.md) and motivated in detail in [`PLAN.md`](PLAN.md).

Before starting work on a track, create or comment on an issue stating your intent and scope to avoid duplicated effort. 
If a track is large, prefer multiple smaller PRs over a single sprawling one.

## Branching

Branch off `main` and preferably name the branch after the track followed by a short description:

```
track-B-sigma-statement
track-D-mac-correctness
track-L1-ideal-functionality
```

Multi-PR work on the same track is fine; suffix with a short variant (e.g., `track-B-sigma-statement-pt2`).

## Build expectations

`lake build` must pass before opening a PR. CI runs the same command and will mark a failing PR as red.

## Suggested PR title format

```
<type>: <subject>
```

`<type>` is one of `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`. Subject uses imperative present tense (`add`, not `added`), no leading capital, no trailing period.

Examples:

```
feat: define algebraic MAC over mixed group/scalar attributes
fix: correct exponent in presentation proof Z=I^z
doc: document KVAC/Core/ API contract
```

## PR footer

The footer is optional and may contain:

- **Breaking changes**, with the description, justification, and migration notes.
- **Issue references**, on a separate line prefixed with `Closes`, e.g. `Closes #123, #456`.

## Review

PRs are reviewed when marked ready (not draft) and all checks pass.
