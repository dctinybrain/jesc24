From Coq Require Import Ascii List String ZArith.
From iris.heap_lang Require Import lang notation.
From iris.tests Require Import jessie_notation.

Import ListNotations.
Open Scope char_scope.
Open Scope string_scope.
Open Scope Z_scope.

(** * Parser for the Jessie fragment used by the makeCounter example *)

Inductive jexpr :=
| EVar (x : string)
| ENum (n : Z)
| EAssignPlus (x : string) (n : Z)
| EAssignMinus (x : string) (n : Z)
| EObject (fields : list (string * jexpr))
| EArrow0Expr (e : jexpr)
| EArrow0Block (ss : list jstmt)
with jstmt :=
| SLet (x : string) (e : jexpr)
| SReturn (e : jexpr).

Inductive jdecl :=
| DConst (x : string) (e : jexpr).

Scheme jexpr_ind' := Induction for jexpr Sort Prop
with jstmt_ind' := Induction for jstmt Sort Prop.
Combined Scheme jsyntax_ind from jexpr_ind', jstmt_ind'.

Definition parser (A : Type) := list ascii -> option (A * list ascii).

Definition parse_error {A : Type} : parser A := fun _ => None.

Definition ret {A : Type} (x : A) : parser A :=
  fun cs => Some (x, cs).

Definition bind {A B : Type} (p : parser A) (k : A -> parser B) : parser B :=
  fun cs =>
    match p cs with
    | Some (x, rest) => k x rest
    | None => None
    end.

Notation "x <- p ;; k" := (bind p (fun x => k))
  (at level 100, p at next level, right associativity).

Definition then_ {A B : Type} (p : parser A) (k : parser B) : parser B :=
  bind p (fun _ => k).

Fixpoint string_chars (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_chars s'
  end.

Definition explode (s : string) : list ascii := string_chars s.

Definition is_space (c : ascii) : bool :=
  orb (Ascii.eqb c " ")
    (orb (Ascii.eqb c (Ascii.ascii_of_nat 9))
       (orb (Ascii.eqb c (Ascii.ascii_of_nat 10))
          (Ascii.eqb c (Ascii.ascii_of_nat 13)))).

Fixpoint skip_ws_chars (cs : list ascii) : list ascii :=
  match cs with
  | c :: rest => if is_space c then skip_ws_chars rest else cs
  | [] => []
  end.

Definition satisfy (f : ascii -> bool) : parser ascii :=
  fun cs =>
    match skip_ws_chars cs with
    | c :: rest => if f c then Some (c, rest) else None
    | [] => None
    end.

Definition char (a : ascii) : parser ascii :=
  satisfy (Ascii.eqb a).

Fixpoint literal_chars (xs : list ascii) : parser unit :=
  match xs with
  | [] => ret tt
  | c :: xs' => then_ (char c) (literal_chars xs')
  end.

Definition literal (s : string) : parser unit := literal_chars (string_chars s).

Definition ascii_is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 65 n) && (Nat.leb n 90)) ||
  ((Nat.leb 97 n) && (Nat.leb n 122)) ||
  Ascii.eqb c "_"%char.

Definition ascii_is_alnum (c : ascii) : bool :=
  ascii_is_alpha c ||
  let n := nat_of_ascii c in
  ((Nat.leb 48 n) && (Nat.leb n 57)).

Definition string_of_ascii_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Fixpoint take_ident (acc : list ascii) (cs : list ascii) : string * list ascii :=
  match cs with
  | c :: rest =>
      if ascii_is_alnum c then take_ident (c :: acc) rest
      else (string_of_ascii_list (rev acc), cs)
  | [] => (string_of_ascii_list (rev acc), [])
  end.

Definition parse_ident : parser string :=
  fun cs =>
    match skip_ws_chars cs with
    | c :: rest =>
        if ascii_is_alpha c then
          let '(name, rest') := take_ident [c] rest in
          Some (name, rest')
        else None
    | [] => None
    end.

Definition digit_value (c : ascii) : option nat :=
  if Ascii.eqb c "0" then Some 0%nat else
  if Ascii.eqb c "1" then Some 1%nat else
  if Ascii.eqb c "2" then Some 2%nat else
  if Ascii.eqb c "3" then Some 3%nat else
  if Ascii.eqb c "4" then Some 4%nat else
  if Ascii.eqb c "5" then Some 5%nat else
  if Ascii.eqb c "6" then Some 6%nat else
  if Ascii.eqb c "7" then Some 7%nat else
  if Ascii.eqb c "8" then Some 8%nat else
  if Ascii.eqb c "9" then Some 9%nat else
  None.

Fixpoint digits_to_nat (acc : nat) (cs : list ascii) : nat * list ascii :=
  match cs with
  | c :: rest =>
      match digit_value c with
      | Some d => digits_to_nat (10 * acc + d)%nat rest
      | None => (acc, cs)
      end
  | [] => (acc, [])
  end.

Definition parse_nat_lit : parser Z :=
  fun cs =>
    match skip_ws_chars cs with
    | c :: rest =>
        match digit_value c with
        | Some d =>
            let '(n, rest') := digits_to_nat d rest in
            Some (Z.of_nat n, rest')
        | None => None
        end
    | [] => None
    end.

Fixpoint parse_expr (fuel : nat) : parser jexpr
with parse_stmt (fuel : nat) : parser jstmt
with parse_stmt_list (fuel : nat) : parser (list jstmt)
with parse_fields (fuel : nat) : parser (list (string * jexpr)).
Proof.
  - destruct fuel as [|fuel']; [exact parse_error|].
    refine (fun cs =>
      let cs := skip_ws_chars cs in
      match cs with
      | "("%char :: ")"%char :: rest1 =>
          let rest1 := skip_ws_chars rest1 in
          match rest1 with
          | "="%char :: ">"%char :: rest2 =>
              let rest2 := skip_ws_chars rest2 in
              match rest2 with
              | "{"%char :: _ =>
                  match parse_stmt_list fuel' rest2 with
                  | Some (ss, rest3) => Some (EArrow0Block ss, rest3)
                  | None => None
                  end
              | _ =>
                  match parse_expr fuel' rest2 with
                  | Some (e, rest3) => Some (EArrow0Expr e, rest3)
                  | None => None
                  end
              end
          | _ =>
              match parse_expr fuel' rest1 with
              | Some (e, rest2) =>
                  match skip_ws_chars rest2 with
                  | ")"%char :: rest3 => Some (e, rest3)
                  | _ => None
                  end
              | None => None
              end
          end
      | "("%char :: rest1 =>
          match parse_expr fuel' rest1 with
          | Some (e, rest2) =>
              match skip_ws_chars rest2 with
              | ")"%char :: rest3 => Some (e, rest3)
              | _ => None
              end
          | None => None
          end
      | "{"%char :: rest1 =>
          match parse_fields fuel' rest1 with
          | Some (fs, rest2) => Some (EObject fs, rest2)
          | None => None
          end
      | _ =>
          match parse_ident cs with
          | Some (x, rest1) =>
              let rest1 := skip_ws_chars rest1 in
              match rest1 with
              | "+"%char :: "="%char :: rest2 =>
                  match parse_nat_lit rest2 with
                  | Some (n, rest3) => Some (EAssignPlus x n, rest3)
                  | None => None
                  end
              | "-"%char :: "="%char :: rest2 =>
                  match parse_nat_lit rest2 with
                  | Some (n, rest3) => Some (EAssignMinus x n, rest3)
                  | None => None
                  end
              | _ => Some (EVar x, rest1)
              end
          | None =>
              match parse_nat_lit cs with
              | Some (n, rest1) => Some (ENum n, rest1)
              | None => None
              end
          end
      end).
  - destruct fuel as [|fuel']; [exact parse_error|].
    refine (fun cs =>
      let cs := skip_ws_chars cs in
      match literal "let" cs with
      | Some (_, rest1) =>
          match parse_ident rest1 with
          | Some (x, rest2) =>
              match skip_ws_chars rest2 with
              | "="%char :: rest3 =>
                  match parse_expr fuel' rest3 with
                  | Some (e, rest4) =>
                      match skip_ws_chars rest4 with
                      | ";"%char :: rest5 => Some (SLet x e, rest5)
                      | _ => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | None => None
          end
      | None =>
          match literal "return" cs with
          | Some (_, rest1) =>
              match parse_expr fuel' rest1 with
              | Some (e, rest2) =>
                  match skip_ws_chars rest2 with
                  | ";"%char :: rest3 => Some (SReturn e, rest3)
                  | _ => None
                  end
              | None => None
              end
          | None => None
          end
      end).
  - destruct fuel as [|fuel']; [exact parse_error|].
    refine (fun cs =>
      match skip_ws_chars cs with
      | "{"%char :: rest =>
          match parse_stmt_list fuel' rest with
          | Some (ss, rest') => Some (ss, rest')
          | None => None
          end
      | "}"%char :: rest => Some ([], rest)
      | _ =>
          match parse_stmt fuel' cs with
          | Some (s, rest1) =>
              match parse_stmt_list fuel' rest1 with
              | Some (ss, rest2) => Some (s :: ss, rest2)
              | None => None
              end
          | None => None
          end
      end).
  - destruct fuel as [|fuel']; [exact parse_error|].
    refine (fun cs =>
      match skip_ws_chars cs with
      | "}"%char :: rest => Some ([], rest)
      | _ =>
          match parse_ident cs with
          | Some (k, rest1) =>
              match skip_ws_chars rest1 with
              | ":"%char :: rest2 =>
                  match parse_expr fuel' rest2 with
                  | Some (e, rest3) =>
                      match skip_ws_chars rest3 with
                      | ","%char :: rest4 =>
                          match skip_ws_chars rest4 with
                          | "}"%char :: rest5 => Some ([(k, e)], rest5)
                          | _ =>
                              match parse_fields fuel' rest4 with
                              | Some (fs, rest5) => Some ((k, e) :: fs, rest5)
                              | None => None
                              end
                          end
                      | "}"%char :: rest4 => Some ([(k, e)], rest4)
                      | _ => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | None => None
          end
      end).
Defined.

Definition parse_expr_only (s : string) : option jexpr :=
  match parse_expr (String.length s + 20)%nat (explode s) with
  | Some (e, rest) =>
      match skip_ws_chars rest with
      | [] => Some e
      | _ => None
      end
  | None => None
  end.

Definition parse_decl_only (s : string) : option jdecl :=
  match literal "const" (explode s) with
  | Some (_, rest1) =>
      match parse_ident rest1 with
      | Some (x, rest2) =>
          match skip_ws_chars rest2 with
          | "="%char :: rest3 =>
              match parse_expr (String.length s + 40)%nat rest3 with
              | Some (e, rest4) =>
                  match skip_ws_chars rest4 with
                  | ";"%char :: rest5 =>
                      match skip_ws_chars rest5 with
                      | [] => Some (DConst x e)
                      | _ => None
                      end
                  | _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | None => None
      end
  | None => None
  end.

Fixpoint compile_expr (env : list string) (hint : option string) (e : jexpr) : expr.
Proof.
  refine (
    match e with
    | EVar x => Var x
    | ENum n => Lit (LitInt n)
    | EAssignPlus x n => op_assign PlusOp (Var x) (Lit (LitInt n))
    | EAssignMinus x n => op_assign MinusOp (Var x) (Lit (LitInt n))
    | EObject fs =>
        j_object (map (fun kv => (fst kv, compile_expr env (Some (fst kv)) (snd kv))) fs)
    | EArrow0Expr e1 =>
        let body := compile_expr env None e1 in
        let rec_name := "f" in
        fold_right (fun x acc => App (Lam (BNamed x) acc) (Var x))
                   (Rec (BNamed rec_name) BAnon body) env
    | EArrow0Block ss1 =>
        let fix compile_block (env' : list string) (ss : list jstmt) : expr :=
            match ss with
            | [] => Unit
            | SLet x e :: ss' =>
                Let (BNamed x) (Alloc (compile_expr env' None e))
                  (compile_block (x :: env') ss')
            | [SReturn e] => compile_expr env' None e
            | SReturn _ :: _ => Unit
            end in
        let body := compile_block env ss1 in
        let rec_name := "f" in
        fold_right (fun x acc => App (Lam (BNamed x) acc) (Var x))
                   (Rec (BNamed rec_name) BAnon body) env
    end).
Defined.

Fixpoint compile_stmt_list (env : list string) (ss : list jstmt) : expr :=
  match ss with
  | [] => Unit
  | SLet x e :: ss' =>
      Let (BNamed x) (Alloc (compile_expr env None e))
        (compile_stmt_list (x :: env) ss')
  | [SReturn e] => compile_expr env None e
  | SReturn _ :: _ => Unit
  end.

Definition compile_decl_body (d : jdecl) : option val :=
  match d with
  | DConst _ (EArrow0Block ss) =>
      let body := compile_stmt_list [] ss in
      if decide (Closed (BAnon :b: BAnon :b: []) body)
      then Some (locked (LamV BAnon body))
      else None
  | _ => None
  end.

Definition compile_parsed_decl_body (s : string) : option val :=
  match parse_decl_only s with
  | Some d => compile_decl_body d
  | None => None
  end.

Definition compile_decl_expr (d : jdecl) : option expr :=
  match d with
  | DConst x e =>
      match compile_decl_body (DConst x e) with
      | Some v => Some (Let (BNamed x) v (Var x))
      | None => None
      end
  end.

Definition compile_parsed_decl_expr (s : string) : option expr :=
  match parse_decl_only s with
  | Some d => compile_decl_expr d
  | None => None
  end.

Example parse_expr_assign_generic :
  parse_expr_only "total += 7" = Some (EAssignPlus "total" 7).
Proof. vm_compute. reflexivity. Qed.

Example parse_expr_object_generic :
  parse_expr_only "{ up: () => (cell += 1), down: () => (cell -= 1), }" =
    Some (EObject
      [("up", EArrow0Expr (EAssignPlus "cell" 1));
       ("down", EArrow0Expr (EAssignMinus "cell" 1))]).
Proof. vm_compute. reflexivity. Qed.
