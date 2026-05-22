jesc24 -- Jessie Escrow formal verification in Coq
====================================================

This repository formalizes JavaScript smart-contract escrow patterns
in Coq.  It provides a compilation pipeline from Jessie (a
capability-secure subset of JavaScript used by the Zoe 2 escrow
service) through PEG-backed parsers and AST lowering to HeapLang,
where robust-safety theorems are proved using the Iris program logic
framework.  The main results so far are a source-linked robust-safety
proof for the makeCounter example and exact-source PEG recognition for
the escrow2013 contract.

The repository started as a fork of the Iris Coq development
supporting the OCPL paper (see History below).  The OCPL foundation
theories (heap_lang, program_logic, base_logic, etc.) are the
platform on which the Jessie proofs are built.


Repository structure
--------------------

theories/jessie/             Active Jessie work (dc-jessie branch)
  jessie_notation.v           Jessie-flavored object/string/update notation
  jessica_ast.v               Jessie abstract syntax tree
  quasi_json.v                PEG parser: quasi-json notation
  quasi_justin.v              PEG parser: quasi-justin notation
  quasi_jessie.v              PEG parser: quasi-jessie notation
  jessica_to_hla.v            Lowering: JessicaAst -> HeapLang AST
  make_counter.v              Parser/lowering facts and robust safety
                              for makeCounter and checkedCounter
  escrow2013_target.v         Constructor-rich JessicaAst target for
                              the escrow2013 rendition
  escrow2013.v                Exact-source PEG recognition for
                              escrow2013_source
  sources/                    Jessie source files (makeCounter.js,
                              escrow2013.js)
  tools/js_to_coq_source.py   Source embedding helper

vendor/peg-coq/               Vendored peg-coq theories (Charset,
                              Match, Suffix, Syntax, Tactics)

theories/heap_lang/           OCPL heap language (HLA) with
                              robust-safety infrastructure
theories/program_logic/       OCPL program logic (progressive /
                              non-progressive weakest preconditions)
theories/base_logic/          Iris base logic and primitive connectives
theories/algebra/             COFE and CMRA constructions
theories/prelude/             Extended standard library
theories/proofmode/           Iris proof mode for Coq
theories/tests/               OCPL example programs and their proofs

docs/                         LaTeX documentation (OCPL paper appendix)
benchmark/                    Build timing benchmarks


Proven results
--------------

On the Jessie side (dc-jessie branch):

  * parse_makeCounter_source_program: makeCounter source parses to the
    constructor-rich makeCounter_jessica_program.
  * jessica_to_hla_makeCounter_is_make_counter_binding: the makeCounter
    Jessica module lowers to a HeapLang binding.
  * parse_checkedCounter_source_program: checkedCounter source parses.
  * jessica_to_hla_checkedCounter_program: the checkedCounter Jessica
    module lowers to checkedCounter_lowered_expr.
  * checked_counter_safe: robust safety for the proof-oriented client
    term.
  * checked_counter_from_source_safe: robust safety for the
    source-linked lowered checked-client shape (the current bridge
    from source-facing Jessie syntax to the OCPL robust-safety proof
    line).
  * parse_escrow2013_source_program: exact-source PEG recognition for
    the escrow2013 source against escrow2013_program.

On the OCPL side (on main):

  * Robust safety theorems for object capability patterns: sealing,
    caretaker, membrane.
  * Derived OCPs and client programs in theories/tests/.
  * The fundamental theorem of logical relations and the "internal"
    version of robust safety.


Build
-----

### Nix (current recommended route)

The repository provides a Nix flake:

  nix develop

This provides Coq 8.9, Python 3, GNU Make, and other needed tools.
Then:

  make -jN

where N is the number of cores.

### Opam (legacy route)

Install Coq 8.9.1 via Opam, then:

  eval "$(opam env --switch=ocpl-coq-8.9.1-ocaml-4.07.1)"
  make -jN

The _CoqProject file lists all source modules.  Generated files
(theories/jessie/*_js.v) are produced by the Makefile, so a clean
checkout should start from top-level make, not from a direct
coq_makefile invocation.


Context / See also
------------------

* Zoe 2 Escrow formal verification spike:
  https://github.com/Agoric/agoric-sdk/pull/8184
  (SPIKE: toward correct-by-construction Zoe2 escrow)

* EndoJS / Jessie parsers in JavaScript:
  https://github.com/endojs/endo/tree/master/packages/jessie

* Presentation-level running example (separation-of-duties
  makeCounter): packages/zoe/spec/jessie-iris.md in the agoric-sdk
  repository.

* OCPL paper: "Robust and Compositional Verification of Object
  Capability Patterns" (2019)


Status
------

The repository has two active lines of work:

  * main branch -- OCPL Coq development (the Iris fork with
    progressive/non-progressive weakest preconditions and the HLA heap
    language).  This is the stable foundation.  It compiles standalone.

  * dc-jessie branch (DRAFT PR #6) -- Jessie formal verification work.
    This branch adds theories/jessie/, vendor/peg-coq/, and associated
    build machinery.  It has NOT been merged to main.

The Jessie work is being prepared for merge.  Once this README is
approved and merged to main, the dc-jessie branch can follow.


History
-------

This repository began as a fork of the Iris Coq development
(http://iris-project.org) started before the Iris 3.0 release,
supporting the paper "Robust and Compositional Verification of Object
Capability Patterns" (OCPL).  The OCPL work modified Iris' sample
program logic to distinguish progressive and non-progressive weakest
preconditions, and Iris' sample heap language to support assertion
expressions for stating robust safety.  The modified heap language is
called HLA.

See ./Iris_README.md for the original Iris build instructions and a
tour of the Iris version we started with.

The active work has since shifted to formal verification of Jessie
escrow patterns, which is the current focus of the repository.
