From Coq Require Import List String ZArith.
From Peg Require Import Match.
From iris.jessie Require Import escrow2013_js.
From iris.jessie Require Import escrow2013_target jessica_ast quasi_jessie.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module Escrow2013.
  Import Escrow2013Target.
  Import JessicaAst.
  Import QuasiJessie.

  (* Current PEG milestone for escrow2013: exact-source recognition wired to a
     separately declared JessicaAst target. This is intentionally narrower
     than the structured makeCounter path until the Jessie grammar grows to
     cover imports, arrays, promise-oriented control flow, and throw. *)
  Definition parse_program_only (s : string) : option jmodule :=
    match run_pat [] (exact_module_source escrow2013_source) 65536 s with
    | Some EmptyString => Some escrow2013_program
    | _ => None
    end.

  Example parse_escrow2013_module_exact :
    matches_comp [] (exact_module_source escrow2013_source) escrow2013_source 65536 =
      Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_escrow2013_source_program :
    parse_program_only escrow2013_source = Some escrow2013_program.
  Proof. vm_compute. reflexivity. Qed.

  Example parse_escrow2013_source_program_structured :
    QuasiJessie.parse_program_only escrow2013_source = Some escrow2013_program.
  Proof. vm_compute. reflexivity. Qed.

  Example escrow2013_source_parses_sound :
    matches [] (exact_module_source escrow2013_source) escrow2013_source
      (Success EmptyString).
  Proof.
    apply (matches_comp_soundness [] (exact_module_source escrow2013_source)
      escrow2013_source 65536).
    exact parse_escrow2013_module_exact.
  Qed.
End Escrow2013.
