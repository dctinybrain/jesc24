From Coq Require Import List String ZArith.
From iris.jessie Require Import escrow2013_js.
From iris.jessie Require Import escrow2013_target jessica_ast quasi_jessie.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module Escrow2013.
  Import Escrow2013Target.
  Import JessicaAst.
  Import QuasiJessie.

  Definition parse_program_only (s : string) : option jmodule :=
    QuasiJessie.parse_program_only s.

  Example parse_escrow2013_source_program :
    parse_program_only escrow2013_source = Some escrow2013_program.
  Proof. vm_compute. reflexivity. Qed.
End Escrow2013.
