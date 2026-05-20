---
created: 2026-05-20
updated: 2026-05-20
author: designer
---

# Repo reorganization: vendor Iris and OCPL materials

| field | value |
|---|---|
| status | draft |
| date | 2026-05-20 |
| scope | directory layout, _CoqProject, Makefile, README references |

## Problem

The jesc24 repository began as a fork of the Iris Coq development, modified to support the OCPL paper. As the project's focus has shifted to Jessie escrow verification, the Iris and OCPL materials have become a vendored foundation rather than the primary content. Currently:

- `Iris_README.md` sits at the top level, describing the Iris project's development structure.
- The entire `theories/` directory (prelude, algebra, base_logic, program_logic, heap_lang, proofmode, tests) is the Iris/OCPL Coq development, occupying the root-level namespace.
- The `README` file on `main` is written from the OCPL/Iris perspective, not the jesc24 perspective.
- The `dc-jessie` branch already introduces `vendor/peg-coq/` for peg-coq theories, establishing a vendor convention.

This layout makes it unclear that jesc24 is the primary project and Iris/OCPL is the platform it builds on. New contributors landing on the repo see Iris documentation before jesc24 content.

## Proposed structure

Move all Iris and OCPL materials under `vendor/iris-coq/`. The top-level repo then represents jesc24 first, with vendored dependencies clearly separated.

### After reorganization

```
README.md                  # jesc24 project README (primary entry point)
_CoqProject                # updated paths for vendored iris-coq
Makefile                   # updated if needed
flake.nix / flake.lock     # unchanged
docs/                      # unchanged (OCPL paper appendix)
benchmark/                 # unchanged
theories/                  # jesc24-specific theories only
  jessie/                  # Jessie work (notation, AST, parsers, lowering, proofs)
  tests/                   # jesc24-specific test proofs (moved from theories/tests/)
vendor/
  iris-coq/                # vendored Iris/OCPL Coq development
    Iris_README.md         # moved from top-level
    ProofMode.md           # moved from top-level
    naming.txt             # moved from top-level
    theories/              # all Iris/OCPL theories
      prelude/
      algebra/
      base_logic/
      program_logic/
      heap_lang/
      proofmode/
      tests/               # OCPL example proofs (sealing, caretaker, membrane, etc.)
  peg-coq/                 # already on dc-jessie branch
    theories/
      Charset.v
      Match.v
      Suffix.v
      Syntax.v
      Tactics.v
```

### What moves

| current path | new path |
|---|---|
| `Iris_README.md` | `vendor/iris-coq/Iris_README.md` |
| `ProofMode.md` | `vendor/iris-coq/ProofMode.md` |
| `naming.txt` | `vendor/iris-coq/naming.txt` |
| `theories/prelude/` | `vendor/iris-coq/theories/prelude/` |
| `theories/algebra/` | `vendor/iris-coq/theories/algebra/` |
| `theories/base_logic/` | `vendor/iris-coq/theories/base_logic/` |
| `theories/program_logic/` | `vendor/iris-coq/theories/program_logic/` |
| `theories/heap_lang/` | `vendor/iris-coq/theories/heap_lang/` |
| `theories/proofmode/` | `vendor/iris-coq/theories/proofmode/` |
| `theories/tests/` | `vendor/iris-coq/theories/tests/` |
| `docs/` | `vendor/iris-coq/docs/` |

### What stays at top level

- `README.md` (the jesc24-oriented README, already drafted on `readme/repo-scope-ocpl-to-jesc`)
- `theories/jessie/` (active Jessie work, currently on `dc-jessie`)
- `benchmark/`, `CHANGELOG.md`, `LICENSE*`, `flake.*`, `.github/`

### The `theories/` directory at top level

After the move, `theories/` at the top level contains only jesc24-specific work (`theories/jessie/`). The OCPL example proofs currently in `theories/tests/` move to `vendor/iris-coq/theories/tests/` since they demonstrate OCPL patterns, not jesc24 results.

If there is a desire to keep a top-level `theories/tests/` for jesc24-specific regression tests, that directory can be created fresh. The existing contents (sealing, caretaker, membrane, barrier_client, etc.) are OCPL examples and belong in the vendor.

## Impact analysis

### `_CoqProject`

The current `_CoqProject` on `main`:

```
-Q theories iris
```

This maps the `theories/` directory to the Coq logical path `iris`. After reorganization, this must change to:

```
-Q vendor/iris-coq/theories iris
```

All file paths listed in `_CoqProject` must be prefixed with `vendor/iris-coq/`. The `-Q` logical path `iris` is preserved, so any `From iris Require ...` imports in downstream code continue to work without change.

On the `dc-jessie` branch, `_CoqProject` also includes:

```
-R vendor/peg-coq/theories Peg
```

This line is unaffected. The peg-coq vendor path remains the same.

After reorganization, `dc-jessie`'s `_CoqProject` would also need to add a line for the jessie theories:

```
-Q theories/jessie jessie
```

(Or whatever logical path the Jessie work uses. This is a separate concern from the vendor reorganization but should be considered when the dc-jessie branch is updated.)

### Makefile

The top-level Makefile delegates to `coq_makefile` via `_CoqProject`:

```makefile
Makefile.coq: _CoqProject Makefile
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq
```

Since `coq_makefile` reads paths from `_CoqProject`, the Makefile itself requires no changes. The generated `Makefile.coq` will reference the correct vendored paths automatically.

### README references

The current `README` on `main` contains paths like:

- `./theories/program_logic/weakestpre.v`
- `./theories/heap_lang/lang.v`
- `./theories/heap_lang/lib/sealing.v`

These must be updated to:

- `./vendor/iris-coq/theories/program_logic/weakestpre.v`
- `./vendor/iris-coq/theories/heap_lang/lang.v`
- `./vendor/iris-coq/theories/heap_lang/lib/sealing.v`

The `Iris_README.md` itself contains internal references (e.g., `[prelude](prelude)`, `[ProofMode.md](ProofMode.md)`). These are relative paths within the Iris README. After moving to `vendor/iris-coq/`, these references remain valid because the entire file moves with its referenced siblings. No update needed inside `Iris_README.md`.

The `README.md` on the `readme/repo-scope-ocpl-to-jesc` branch already describes the structure with `vendor/` in mind (it mentions `vendor/peg-coq/`). It should be updated to reflect the new `vendor/iris-coq/` layout in its repository structure section.

### Coq source files

The Iris/OCPL `.v` files use `From iris Require ...` imports, which resolve via the `-Q theories iris` mapping. Since the logical path `iris` is preserved (only the physical directory changes), no `.v` file content needs modification.

Any jessie-side code that imports from iris (e.g., `From iris Require Import program_logic.weakestpre.`) continues to work unchanged.

### Branch strategy

The reorganization should land on `main` first, since `main` is the foundation that other branches build on. The affected branches:

1. **`main`** — primary target. Move Iris/OCPL materials to `vendor/iris-coq/`, update `_CoqProject` and `README`.
2. **`dc-jessie`** — must be rebased onto the reorganized `main`. The `vendor/peg-coq/` directory is unaffected. The `_CoqProject` on this branch needs the same iris path update plus any jessie-specific additions.
3. **`readme/repo-scope-ocpl-to-jesc`** — the README.md structure section should be updated to reflect `vendor/iris-coq/`.
4. **`dc-ci`, `dc-jessie-ci`, `refactor/parser-grammar`** — rebase onto reorganized `main` as needed.

## Alternatives considered

### Keep Iris/OCPL at top level, add vendor/iris-coq as a submodule

Rejected. A git submodule adds operational complexity (init, update, pinning) for content that is already in the repo and modified for OCPL. The fork relationship is historical; the OCPL modifications are committed in this repo. A submodule would require extracting the OCPL changes into a separate repo, which is unnecessary scope.

### Rename `theories/` to `vendor/iris-coq/theories/` but keep `Iris_README.md` at top level

Rejected. The `Iris_README.md` describes the Iris directory structure. If `theories/` moves, the README's descriptions no longer match the top-level layout. Moving the README with the content it describes keeps the documentation coherent.

### Flatten: merge Iris/OCPL theories into a single `vendor/iris-coq/` without subdirectories

Rejected. The Iris directory structure (prelude, algebra, base_logic, etc.) is well-established and referenced throughout the Coq sources and external documentation. Preserving the internal layout minimizes disruption and keeps `-Q` logical path mapping straightforward.

## Migration steps

1. On a `design/repo-org` branch from `main`:
   a. Create `vendor/iris-coq/` directory.
   b. Move `Iris_README.md`, `ProofMode.md`, `naming.txt` into `vendor/iris-coq/`.
   c. Move `theories/` into `vendor/iris-coq/theories/`.
   d. Update `_CoqProject`: prefix all `theories/` paths with `vendor/iris-coq/`.
   e. Update `README`: fix all paths that reference moved files.
   f. Verify `make` succeeds with the updated `_CoqProject`.
2. Open a draft PR against `main`.
3. After merge, rebase `dc-jessie` and other dependent branches.

## Resolved decisions

1. **`theories/tests/` moves to `vendor/iris-coq/theories/tests/`.** The OCPL example proofs (sealing, caretaker, membrane) are self-contained and compile against the vendored iris theories — they go with the rest of the vendored material.

2. **The `-Q` logical path stays `iris`.** Minimizes disruption to import statements across the codebase.

3. **`docs/` moves to `vendor/iris-coq/docs/`.** The LaTeX source (`iris.tex`) is the Iris paper appendix, not jesc24 project documentation — it belongs with the vendored Iris material.
