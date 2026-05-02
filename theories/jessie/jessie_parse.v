From Coq Require Import Ascii List String ZArith.
From iris.heap_lang Require Import lang notation.
From iris.jessie Require Import jessie_notation.

Import ListNotations.
Open Scope char_scope.
Open Scope string_scope.
Open Scope Z_scope.

(** * Legacy parser for the Jessie fragment - superseded by quasi_jessie.v
    This parser was used in earlier versions but has been replaced by the
    PEG-based parser in quasi_jessie.v. The active makeCounter source-to-HLA
    path in make_counter.v now uses quasi_jessie instead.
    
    This file is kept for reference but should not be used for new developments. *)

Inductive jexpr :=
| EVar (x : string)
| ENum (n : Z)
| EOpAssign (op : bin_op) (x : string) (n : Z)
| EGet (e : jexpr) (k : string)
| ECall (e : jexpr) (args : list jexpr)
| EGreater (e1 e2 : jexpr)
| EObject (fields : list (string * jexpr))
| EArrow (params : list string) (body : jarrow_body)
with jstmt :=
| SLet (x : string) (e : jexpr)
| SConst (x : string) (e : jexpr)
| SExpr (e : jexpr)
| SAssert (e : jexpr)
| SReturn (e : jexpr)
with jarrow_body :=
| JArrowExpr (e : jexpr)
| JArrowBlock (ss : list jstmt).

Inductive jdecl :=
| DConst (x : string) (e : jexpr).

Scheme jexpr_ind' := Induction for jexpr Sort Prop
with jstmt_ind' := Induction for jstmt Sort Prop
with jarrow_body_ind' := Induction for jarrow_body Sort Prop.
Combined Scheme jsyntax_ind from jexpr_ind', jstmt_ind', jarrow_body_ind'.

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
      let fix parse_param_list (fuel0 : nat) (cs : list ascii)
        {struct fuel0} : option (list string * list ascii) :=
          match fuel0 with
          | O => None
          | S fuel1 =>
              let cs := skip_ws_chars cs in
              match cs with
              | ")"%char :: rest => Some ([], rest)
              | _ =>
                  match parse_ident cs with
                  | Some (x, rest1) =>
                      let rest1 := skip_ws_chars rest1 in
                      match rest1 with
                      | ","%char :: rest2 =>
                          match parse_param_list fuel1 rest2 with
                          | Some (xs, rest3) => Some (x :: xs, rest3)
                          | None => None
                          end
                      | ")"%char :: rest2 => Some ([x], rest2)
                      | _ => None
                      end
                  | None => None
                  end
              end
          end in
      let fix parse_arg_list (fuel0 : nat) (cs : list ascii)
        {struct fuel0} : option (list jexpr * list ascii) :=
          match fuel0 with
          | O => None
          | S fuel1 =>
              let cs := skip_ws_chars cs in
              match cs with
              | ")"%char :: rest => Some ([], rest)
              | _ =>
                  match parse_expr fuel' cs with
                  | Some (arg, rest1) =>
                      let rest1 := skip_ws_chars rest1 in
                      match rest1 with
                      | ","%char :: rest2 =>
                          match parse_arg_list fuel1 rest2 with
                          | Some (args, rest3) => Some (arg :: args, rest3)
                          | None => None
                          end
                      | ")"%char :: rest2 => Some ([arg], rest2)
                      | _ => None
                      end
                  | None => None
                  end
              end
          end in
      let parse_postfixes (e : jexpr) (cs : list ascii) : option (jexpr * list ascii) :=
          let cs := skip_ws_chars cs in
          let e_and_rest :=
            match cs with
            | "."%char :: rest1 =>
                match parse_ident rest1 with
                | Some (k, rest2) =>
                    let e1 := EGet e k in
                    match skip_ws_chars rest2 with
                    | "("%char :: rest3 =>
                        match parse_arg_list fuel' rest3 with
                        | Some (args, rest4) => Some (ECall e1 args, rest4)
                        | None => None
                        end
                    | _ => Some (e1, rest2)
                    end
                | None => None
                end
            | "("%char :: rest1 =>
                match parse_arg_list fuel' rest1 with
                | Some (args, rest2) => Some (ECall e args, rest2)
                | None => None
                end
            | _ => Some (e, cs)
            end in
          match e_and_rest with
          | Some (e1, rest1) =>
              match skip_ws_chars rest1 with
              | ">"%char :: rest2 =>
                  match parse_expr fuel' rest2 with
                  | Some (e2, rest3) => Some (EGreater e1 e2, rest3)
                  | None => None
                  end
              | _ => Some (e1, rest1)
              end
          | None => None
          end in
      let cs := skip_ws_chars cs in
      match cs with
      | "("%char :: rest1 =>
          match parse_param_list fuel' rest1 with
          | Some (params, rest2) =>
              let rest2 := skip_ws_chars rest2 in
              match rest2 with
              | "="%char :: ">"%char :: rest3 =>
                  let rest3 := skip_ws_chars rest3 in
                  match rest3 with
                  | "{"%char :: _ =>
                      match parse_stmt_list fuel' rest3 with
                      | Some (ss, rest4) => Some (EArrow params (JArrowBlock ss), rest4)
                      | None => None
                      end
                  | _ =>
                      match parse_expr fuel' rest3 with
                      | Some (e, rest4) => Some (EArrow params (JArrowExpr e), rest4)
                      | None => None
                      end
                  end
              | _ =>
                  match parse_expr fuel' rest1 with
                  | Some (e, rest3) =>
                      match skip_ws_chars rest3 with
                      | ")"%char :: rest4 => parse_postfixes e rest4
                      | _ => None
                      end
                  | None => None
                  end
              end
          | None =>
              match parse_expr fuel' rest1 with
              | Some (e, rest2) =>
                  match skip_ws_chars rest2 with
                  | ")"%char :: rest3 => parse_postfixes e rest3
                  | _ => None
                  end
              | None => None
              end
          end
      | "{"%char :: rest1 =>
          match parse_fields fuel' rest1 with
          | Some (fs, rest2) => parse_postfixes (EObject fs) rest2
          | None => None
          end
      | _ =>
          match parse_ident cs with
          | Some (x, rest1) =>
              let rest1 := skip_ws_chars rest1 in
              match rest1 with
              | "="%char :: ">"%char :: rest2 =>
                  let rest2 := skip_ws_chars rest2 in
                  match rest2 with
                  | "{"%char :: _ =>
                      match parse_stmt_list fuel' rest2 with
                      | Some (ss, rest3) => Some (EArrow [x] (JArrowBlock ss), rest3)
                      | None => None
                      end
                  | _ =>
                      match parse_expr fuel' rest2 with
                      | Some (e, rest3) => Some (EArrow [x] (JArrowExpr e), rest3)
                      | None => None
                      end
                  end
              | "+"%char :: "="%char :: rest2 =>
                  match parse_nat_lit rest2 with
                  | Some (n, rest3) => Some (EOpAssign PlusOp x n, rest3)
                  | None => None
                  end
              | "-"%char :: "="%char :: rest2 =>
                  match parse_nat_lit rest2 with
                  | Some (n, rest3) => Some (EOpAssign MinusOp x n, rest3)
                  | None => None
                  end
              | _ => parse_postfixes (EVar x) rest1
              end
          | None =>
              match parse_nat_lit cs with
              | Some (n, rest1) => parse_postfixes (ENum n) rest1
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
          match literal "const" cs with
          | Some (_, rest1) =>
              match parse_ident rest1 with
              | Some (x, rest2) =>
                  match skip_ws_chars rest2 with
                  | "="%char :: rest3 =>
                      match parse_expr fuel' rest3 with
                      | Some (e, rest4) =>
                          match skip_ws_chars rest4 with
                          | ";"%char :: rest5 => Some (SConst x e, rest5)
                          | _ => None
                          end
                      | None => None
                      end
                  | _ => None
                  end
              | None => None
              end
          | None =>
              match literal "assert" cs with
              | Some (_, rest1) =>
                  match skip_ws_chars rest1 with
                  | "("%char :: rest2 =>
                      match parse_expr fuel' rest2 with
                      | Some (e, rest3) =>
                          match skip_ws_chars rest3 with
                          | ")"%char :: ";"%char :: rest4 => Some (SAssert e, rest4)
                          | _ => None
                          end
                      | None => None
                      end
                  | _ => None
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
                  | None =>
                      match parse_expr fuel' cs with
                      | Some (e, rest1) =>
                          match skip_ws_chars rest1 with
                          | ";"%char :: rest2 => Some (SExpr e, rest2)
                          | _ => None
                          end
                      | None => None
                      end
                  end
              end
          end
      end).
  - destruct fuel as [|fuel']; [exact parse_error|].
    refine (fun cs =>
      match skip_ws_chars cs with
      | [] => Some ([], [])
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
    | EOpAssign op x n => op_assign op (Var x) (Lit (LitInt n))
    | EGet e1 k => obj_get (compile_expr env None e1) (j_string k)
    | ECall e1 [] => App (compile_expr env None e1) Unit
    | ECall e1 args =>
        fold_left (fun acc arg => App acc (compile_expr env None arg))
                  args (compile_expr env None e1)
    | EGreater e1 e2 => BinOp LtOp (compile_expr env None e2) (compile_expr env None e1)
    | EObject fs =>
        j_object (map (fun kv => (fst kv, compile_expr env (Some (fst kv)) (snd kv))) fs)
    | EArrow params body1 =>
        let fix compile_block (env' : list string) (ss : list jstmt) : expr :=
            match ss with
            | [] => Unit
            | SLet y e :: ss' =>
                Let (BNamed y) (Alloc (compile_expr env' None e))
                  (compile_block (y :: env') ss')
            | SConst y e :: ss' =>
                Let (BNamed y) (compile_expr env' None e)
                  (compile_block (y :: env') ss')
            | SExpr e :: ss' =>
                Let BAnon (compile_expr env' None e)
                  (compile_block env' ss')
            | SAssert e :: ss' =>
                Let BAnon (Assert (compile_expr env' None e))
                  (compile_block env' ss')
            | [SReturn e] => compile_expr env' None e
            | SReturn _ :: _ => Unit
            end in
        let closed_env := (rev params ++ env)%list in
        let body :=
          match body1 with
          | JArrowExpr e1 => compile_expr closed_env None e1
          | JArrowBlock ss1 => compile_block closed_env ss1
          end in
        let rec_name := "f" in
        let rec_body :=
          match params with
          | [] => Rec (BNamed rec_name) BAnon body
          | x :: xs =>
              Rec (BNamed rec_name) (BNamed x)
                (fold_right (fun y acc => Lam (BNamed y) acc) body xs)
          end in
        fold_right (fun x acc => App (Lam (BNamed x) acc) (Var x))
                   rec_body env
    end).
Defined.

Fixpoint compile_stmt_list (env : list string) (ss : list jstmt) : expr :=
  match ss with
  | [] => Unit
  | SLet x e :: ss' =>
      Let (BNamed x) (Alloc (compile_expr env None e))
        (compile_stmt_list (x :: env) ss')
  | SConst x e :: ss' =>
      Let (BNamed x) (compile_expr env None e)
        (compile_stmt_list (x :: env) ss')
  | SExpr e :: ss' =>
      Let BAnon (compile_expr env None e)
        (compile_stmt_list env ss')
  | SAssert e :: ss' =>
      Let BAnon (Assert (compile_expr env None e))
        (compile_stmt_list env ss')
  | [SReturn e] => compile_expr env None e
  | SReturn _ :: _ => Unit
  end.

Definition compile_decl_body (d : jdecl) : option val :=
  match d with
  | DConst _ (EArrow [] (JArrowBlock ss)) =>
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

Definition parse_program_only (s : string) : option (list jstmt) :=
  match parse_stmt_list (String.length s + 40)%nat (explode s) with
  | Some (ss, rest) =>
      match skip_ws_chars rest with
      | [] => Some ss
      | _ => None
      end
  | None => None
  end.

Definition compile_program_expr (ss : list jstmt) : expr :=
  compile_stmt_list [] ss.

Definition compile_parsed_program_expr (s : string) : option expr :=
  match parse_program_only s with
  | Some ss => Some (compile_program_expr ss)
  | None => None
  end.

Example parse_expr_assign_generic :
  parse_expr_only "total += 7" = Some (EOpAssign PlusOp "total" 7).
Proof. vm_compute. reflexivity. Qed.

Example parse_expr_object_generic :
  parse_expr_only "{ up: () => (cell += 1), down: () => (cell -= 1), }" =
    Some (EObject
      [("up", EArrow [] (JArrowExpr (EOpAssign PlusOp "cell" 1)));
       ("down", EArrow [] (JArrowExpr (EOpAssign MinusOp "cell" 1)))]).
Proof. vm_compute. reflexivity. Qed.
