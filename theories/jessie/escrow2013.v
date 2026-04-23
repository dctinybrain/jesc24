From Coq Require Import List String ZArith.
From iris.jessie.peg Require Import peg_match.
From iris.jessie Require Import escrow2013_target jessica_ast quasi_jessie.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition escrow2013_source : string :=
  "import { E } from '@endo/far';

const Q = Promise;

const Qjoin = harden((p1, p2) =>
  Q.all([p1, p2]).then(([r1, r2]) => {
    if (!Object.is(r1, r2)) {
      throw Error('join failed');
    }
    return r1;
  })
);

const transfer = harden((decisionP, srcPurseP, dstPurseP, amount) => {
  const makeEscrowPurseP = Qjoin(
    E.get(srcPurseP).makePurse,
    E.get(dstPurseP).makePurse
  );
  const escrowPurseP = E(makeEscrowPurseP)();
  // setup phase 2
  Q(decisionP).then(
    _ => {
      E(dstPurseP).deposit(amount, escrowPurseP);
    },
    _ => {
      E(srcPurseP).deposit(amount, escrowPurseP);
    }
  );
  return E(escrowPurseP).deposit(amount, srcPurseP); // phase 1
});

const failOnly = harden(cancellationP =>
  Q(cancellationP).then(cancellation => {
    throw cancellation;
  })
);

// a from Alice , b from Bob
const escrowExchange = harden((a, b) => {
  let decide;
  const decisionP = Q.promise(resolve => {
    decide = resolve;
  });
  decide(
    Q.race([
      Q.all([
        transfer(decisionP, a.moneySrcP, b.moneyDstP, b.moneyNeeded),
        transfer(decisionP, b.stockSrcP, a.stockDstP, a.stockNeeded),
      ]),
      failOnly(a.cancellationP),
      failOnly(b.cancellationP),
    ])
  );
  return decisionP;
});
".

Module Escrow2013.
  Import Escrow2013Target.
  Import JessicaAst.
  Import QuasiJessie.

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

  Example escrow2013_source_parses_sound :
    matches [] (exact_module_source escrow2013_source) escrow2013_source
      (Success EmptyString).
  Proof.
    apply (matches_comp_soundness [] (exact_module_source escrow2013_source)
      escrow2013_source 65536).
    exact parse_escrow2013_module_exact.
  Qed.
End Escrow2013.
