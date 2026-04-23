# Jessie Work In `theories/jessie/`

Current result:
- `make_counter.v` now lives in `theories/jessie/` and still carries the upward-capability counter robust-safety proof line.
- The same directory now also contains a `peg`-based Jessie parser line:
  - `make_counter.v` proves a structured PEG-backed parse of `makeCounter_source` into `JessicaAst`.
  - `escrow2013.v` proves an exact-source PEG parse of `escrow2013_source` into `escrow2013_program`.

The directory currently has three layers:

1. Legacy Jessie-to-HeapLang compatibility path
- `jessie_notation.v`
- `jessie_parse.v`
- the legacy parser/compiler surface used by `make_counter.v`

2. PEG-backed Jessie parser path
- `peg/`: minimal vendored PEG library slice needed by the current parser
- `jessica_ast.v`
- `quasi_json.v`
- `quasi_justin.v`
- `quasi_jessie.v`

3. Example targets and proofs
- `make_counter.v`
- `escrow2013_target.v`
- `escrow2013.v`

Current limitations:
- `makeCounter` goes through the current structured PEG grammar.
- `escrow2013` currently uses an exact-source PEG wrapper via `exact_module_source`; it is not yet parsed by a fully structured Jessie grammar.
- `jessie_parse.v` remains as the legacy `list jstmt -> HeapLang` bridge used by the existing robust-safety result. The PEG/Jessica path has not yet replaced that compiler path.

Build:
- Use the same switch the OCPL proof line uses:
  `eval "$(opam env --switch=ocpl-coq-8.9.1-ocaml-4.07.1)"`
- Then build from `packages/zoe/spec/_research/ocpl-coq/` with `make`.
