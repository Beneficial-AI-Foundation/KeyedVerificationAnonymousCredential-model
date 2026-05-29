# KVAC Verso Documentation

Verso/Blueprint documentation for the `KVAC` Lean library — a paper-driven
formalisation of Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
[IACR ePrint 2024/1552](https://eprint.iacr.org/2024/1552) (cited as O24).

The site mirrors the paper's section structure (and the `KVAC/` source tree),
one chapter per `KVAC/` top-level subdirectory:

| Chapter | Subdir | Track | Paper |
|---|---|---|---|
| [Core](KVACDocs/DocCore.lean) | `KVAC/Core/` | 0 | (algebraic primitives) |
| [Preliminaries](KVACDocs/DocPreliminaries.lean) | `KVAC/Preliminaries/` | Pre | §3 |
| [Proof systems](KVACDocs/DocProofSystems.lean) | `KVAC/ProofSystems/` | Σ | §9 |
| [Framework](KVACDocs/DocFramework.lean) | `KVAC/Framework/` | F1, F2 | §4 |
| [μCMZ](KVACDocs/DocMicroCMZ.lean) | `KVAC/Schemes/MicroCMZ/` | CMZ-* | §5 |
| [μBBS](KVACDocs/DocMicroBBS.lean) | `KVAC/Schemes/MicroBBS/` | BBS-* | §6 |
| [Concrete run](KVACDocs/DocConcreteRun.lean) | `KVAC/{Instances,Examples}/` | Ex | (Track Ex) |

Companion documents in this directory:

- [PLAN.md](PLAN.md) — formalisation plan; the canonical source of the
  per-chapter content below.
- [TRACKS.md](TRACKS.md) — work breakdown by track and current status.
- [STYLE_GUIDE.md](STYLE_GUIDE.md) — Lean style conventions, including the
  prime-order-group binder block.
- [WORKFLOW_AND_PR_GUIDE.md](WORKFLOW_AND_PR_GUIDE.md) — PR / commit
  workflow.

## Quick build

The build + render flow is wrapped in `scripts/build-blueprint.sh`. From
the repository root:

```bash
./scripts/build-blueprint.sh
python3 -m http.server 8080 -d docs/_out/site/html-multi
```

Then open `http://localhost:8080`. The sections below describe what the
wrapper does step by step, useful when debugging or running individual
stages.

## Build

From the repository root:

```bash
lake -d docs update
lake -d docs exe cache get
lake -d docs build KVACDocs Main
```

## Render

From the repository root:

```bash
lake -d docs env lean --run docs/Main.lean --output docs/_out/site
python3 -m http.server 8000 -d docs/_out/site/html-multi
```

Then open `http://localhost:8000`.

The docs import live VCV-io / KVAC modules; if a Lean declaration in a
referenced module is renamed or removed, the documentation build should fail
rather than silently drift.

Avoid `lake -d docs build docs` on checkouts without the vendored native
sources of any dependency that links extern libraries. Building the executable
links the root package's extern libraries; `lake -d docs build KVACDocs Main`
and `lean --run` avoid that link step.

## Adding a new chapter

Each chapter lives in its own file under `docs/KVACDocs/`. To add one:

1. Create `docs/KVACDocs/Doc<Name>.lean` with a chapter scaffold (see
   template below).
2. In both `docs/KVACDocs.lean` and `docs/KVACDocs/Contents.lean`:
   - add `import KVACDocs.Doc<Name>` near the top, and
   - in `Contents.lean`, add `{include 1 KVACDocs.Doc<Name>}` to the body
     where the chapter should appear.
3. Run `./scripts/build-blueprint.sh` to verify the chapter compiles
   and that every `(lean := "...")` reference resolves. The build fails
   if a referenced Lean declaration is missing or renamed, so this is
   also the cheapest way to catch drift between docs and code.

### Minimal chapter scaffold

```lean
/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
-- Plus any KVAC / VCVio modules whose declarations this chapter
-- references via `(lean := "X")`.

open Verso.Genre Manual
open Informal

#doc (Manual) "<Chapter title>" =>
%%%
tag := "<chapter_tag>"
%%%

Prose introduction to the chapter.

:::group "<group_tag>"
Short overview of what the group covers.
:::

:::definition "<def_tag>" (lean := "KVAC.Core.MyLeanDecl") (parent := "<group_tag>")
Description of the definition. The `(lean := ...)` reference must
resolve to a real declaration; the build fails otherwise.
:::
```

### Worked examples

- [`DocCore.lean`](KVACDocs/DocCore.lean) — chapter with a mix of real
  `(lean := ...)`-backed definitions (the two prime-order-group
  `class abbrev`s) and TODO groups for files that have not yet landed.
- [`DocFramework.lean`](KVACDocs/DocFramework.lean) — fully TODO chapter,
  shape mirrors the four-file structure of `KVAC/Framework/`.
