From iris.prelude Require Import strings list.
From iris.heap_lang Require Import heap notation.
From iris.heap_lang.lib Require Import abort.

Open Scope string_scope.

(** * Jessie-flavored encodings on top of HeapLang values *)

Definition object_tag : Z := 1.
Definition string_tag : Z := 2.

Definition j_string (s : string) : val :=
  (#string_tag, #(Z.pos (string_to_pos s))).

Definition incr_key : val := j_string "incr".
Definition decr_key : val := j_string "decr".

Definition op_assign (op : bin_op) (lhs rhs : expr) : expr :=
  App
    (Lam (BNamed "__assign_old")
      (App
        (Lam (BNamed "__assign_new")
          (App
            (Lam BAnon (Var "__assign_new"))
            (Store lhs (Var "__assign_new"))))
        (BinOp op (Var "__assign_old") rhs)))
    (Load lhs).

Fixpoint j_fields (kvs : list (string * expr)) : expr :=
  match kvs with
  | [] => ()
  | (k, v) :: kvs => ((j_string k, v), j_fields kvs)
  end.

Fixpoint j_fieldsV (kvs : list (string * val)) : val :=
  match kvs with
  | [] => ()
  | (k, v) :: kvs => ((j_string k, v), j_fieldsV kvs)
  end.

Definition j_object (kvs : list (string * expr)) : expr :=
  (#object_tag, j_fields kvs).

Definition j_objectV (kvs : list (string * val)) : val :=
  (#object_tag, j_fieldsV kvs).

Definition j_object1 (k : string) (v : expr) : expr :=
  j_object ((k, v) :: nil).

Definition j_object2 (k1 : string) (v1 : expr) (k2 : string) (v2 : expr) : expr :=
  j_object ((k1, v1) :: (k2, v2) :: nil).

Definition j_objectV1 (k : string) (v : val) : val :=
  j_objectV ((k, v) :: nil).

Definition j_objectV2 (k1 : string) (v1 : val) (k2 : string) (v2 : val) : val :=
  j_objectV ((k1, v1) :: (k2, v2) :: nil).

Definition obj_get_fields : val := rec: "obj_get_fields" "fields" "key" :=
  if: "fields" = () then abort
  else
    let: "kv" := Fst "fields" in
    let: "rest" := Snd "fields" in
    if: Fst "kv" = "key" then Snd "kv" else "obj_get_fields" "rest" "key".

Definition obj_get : val := λ: "obj" "key",
  let: "tag" := Fst "obj" in
  let: "fields" := Snd "obj" in
  assert: "tag" = #object_tag ;; obj_get_fields "fields" "key".

Notation "'jobj' [ ]" := (j_object [])
  (at level 0) : expr_scope.
Notation "'jobj' [ k := v ]" :=
  (Pair #object_tag (Pair (Pair (j_string k%string) v%E) Unit))
  (at level 0, k at level 1, v at level 200) : expr_scope.
Notation "'jobj' [ k1 := v1 ; k2 := v2 ]" :=
  (Pair #object_tag
    (Pair (Pair (j_string k1%string) v1%E)
      (Pair (Pair (j_string k2%string) v2%E) Unit)))
  (at level 0, k1 at level 1, v1 at level 200, k2 at level 1, v2 at level 200) : expr_scope.

Notation "e '@[' k ']'" := (obj_get e%E (j_string k%string))
  (at level 20, format "e @[ k ]") : expr_scope.

(* The old Closed instance does not unfold op_assign through rec bodies,
   so keep the update notations expanded at parse time. *)
Notation "e1 += e2" := (
  App
    (Lam (BNamed "__assign_old")
      (App
        (Lam (BNamed "__assign_new")
          (App
            (Lam BAnon (Var "__assign_new"))
            (Store e1%E (Var "__assign_new"))))
        (BinOp PlusOp (Var "__assign_old") e2%E)))
    (Load e1%E)
)
  (at level 80, format "e1  +=  e2") : expr_scope.

Notation "e1 -= e2" := (
  App
    (Lam (BNamed "__assign_old")
      (App
        (Lam (BNamed "__assign_new")
          (App
            (Lam BAnon (Var "__assign_new"))
            (Store e1%E (Var "__assign_new"))))
        (BinOp MinusOp (Var "__assign_old") e2%E)))
    (Load e1%E)
)
  (at level 80, format "e1  -=  e2") : expr_scope.
