# AGENTS.md

## Cursor Cloud specific instructions

### Overview

CompPoly is a formally verified Lean 4 library for computable polynomial operations over finite fields and general rings. There are no servers, databases, or runtime services — the entire "application" is the Lean 4 type-checker and proof verifier.

### Tech stack

- **Language:** Lean 4 (version pinned in `lean-toolchain`, currently v4.28.0)
- **Build system:** Lake (ships with Lean)
- **Toolchain manager:** elan (installed at `~/.elan/bin`)
- **Key dependencies:** Mathlib4, ExtTreeMapLemmas (pinned in `lakefile.lean`)

### Build & test

A successful `lake build` type-checks all source files and verifies all proofs — this is both the build and the test for this project.

```
lake build
```

### Lint

- **Style lint:** `./scripts/lint-style.sh` — runs Python-based style checks (copyright headers, line length, formatting). Requires Python 3.
- **Import check:** `./scripts/check-imports.sh` — verifies `CompPoly.lean` has up-to-date, sorted imports. Fix with `./scripts/update-lib.sh`.

### Non-obvious caveats

- **Mathlib cache is essential:** Always run `lake exe cache get` before `lake build`. Without the pre-built Mathlib cache, building from source takes many hours and 16+ GB RAM.
- **elan must be on PATH:** elan is installed at `~/.elan/bin`. The update script ensures it is on PATH via `~/.bashrc`.
- **`check-imports.sh` may fail on the repo's current state** if `CompPoly.lean` imports are not alphabetically sorted or a new file was added. This is a pre-existing repo issue, not an environment problem. Fix with `./scripts/update-lib.sh` if needed.
- **Build warnings are expected:** Some files produce deprecation warnings or linter notices (e.g., `linter.style.longFile`, `unusedSimpArgs`). These do not indicate build failure.
- **No runtime or dev server:** There is nothing to "start" — `lake build` is the sole development command. The Lean Language Server (provided by elan) is the IDE integration.
