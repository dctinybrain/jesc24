From Coq Require Import Lists.List Strings.Ascii Strings.String ZArith.
From Peg Require Import Charset Syntax Match.
From iris.jessie Require Import jessica_ast quasi_json quasi_justin.

Import ListNotations.
Open Scope string_scope.

Module QuasiJessie.
  Import JessicaAst.
  Import QuasiJson.
  Import QuasiJustin.

  (* String literal: matches '...' (single quoted, no escape handling) *)
  Definition string_lit_single : pat :=
    seq (sym "'")
      (seq (star (seq (PNot (sym "'")) (PSet fullcharset)))
            (sym "'")).

  Definition string_lit : pat := tok string_lit_single.

  (* Import statement: import { x } from 'path'; *)
  Definition import_stmt : pat :=
    seq (kw "import")
      (seq (sym "{")
        (seq ident
          (seq (sym "}")
            (seq (kw "from")
              (seq string_lit (sym ";")))))).

  (* Experimental peg-coq Jessie layer, parallel to quasi-jessie, but only
     broad enough for the current makeCounter path. The PEG definitions below
     are the sole grammar for this workspace; they run over the vendored
     peg-coq slice under vendor/peg-coq/theories, imported here through the
     upstream-style Peg namespace, and the AST helpers later in the file
     build JessicaAst terms by consuming those PEG matches. *)

  (* quasi-jessie.js.ts: lValue <- ... ; here narrowed to identifiers only. *)
  Definition lvalue : pat := ident.

  Definition op_assign : pat :=
    seq lvalue
      (seq (alt (sym "+=") (sym "-=")) (PNT 0)).

  Definition paren_expr : pat :=
    seq (sym "(") (seq (PNT 0) (sym ")")).

  (* quasi-jessie.js.ts: record <- LEFT_BRACE propDef ** _COMMA _COMMA? RIGHT_BRACE *)
  Definition object_pat : pat :=
    seq (sym "{")
      (seq
        (opt
          (seq (PNT 2)
            (seq (star (seq (sym ",") (PNT 2)))
              (opt (sym ",")))))
        (sym "}")).

  Definition comma_list (elem : pat) : pat :=
    seq elem (star (seq (sym ",") elem)).

  Definition arrow_params : pat :=
    seq (sym "(") (seq (opt (comma_list ident)) (sym ")")).

  Definition arrow_body : pat :=
    alt (PNT 4)
      (alt paren_expr (PNT 0)).

  (* quasi-jessie.js.ts:
     arrowFunc <- arrowParams _NO_NEWLINE ARROW block
                / arrowParams _NO_NEWLINE ARROW assignExpr;
  *)
  Definition arrow_func : pat :=
    seq arrow_params
      (seq (sym "=>") arrow_body).

  (* quasi-jessie.js.ts:
     memberPostOp / callPostOp extensions inherited from Justin.
  *)
  Definition expr_post_op : pat := QuasiJustin.post_op 0.

  Definition less_than : pat :=
    seq (PNT 1)
      (seq (star expr_post_op)
        (seq (sym "<")
          (seq (PNT 1) (star expr_post_op)))).

  Definition const_decl : pat :=
    seq (kw "const")
      (seq ident
        (seq (sym "=")
          (seq (PNT 0) (sym ";")))).

  Definition let_decl : pat :=
    seq (kw "let")
      (seq ident
        (seq (sym "=")
          (seq (PNT 0) (sym ";")))).

  (* quasi-jessie.js.ts: returnStatement production subset. *)
  Definition return_stmt : pat :=
    seq (kw "return") (seq (PNT 0) (sym ";")).

  (* Throw statement: throw expr; *)
  Definition throw_stmt : pat :=
    seq (kw "throw") (seq (PNT 0) (sym ";")).

  (* If statement: if (cond) then_branch else else_branch *)
  Definition if_stmt : pat :=
    seq (kw "if")
      (seq (sym "(")
        (seq (PNT 0)  (* condition *)
          (seq (sym ")")
            (seq (PNT 4)  (* then branch - block *)
              (opt (seq (kw "else") (PNT 4))))))).  (* optional else - block *)

  (* quasi-jessie.js.ts: exprStatement <- ~cantStartExprStatement expr SEMI. *)
  Definition expr_stmt : pat := seq (PNT 0) (sym ";").

  Definition assert_stmt : pat :=
    seq (kw "assert")
      (seq (sym "(")
        (seq (PNT 0)
          (seq (sym ")") (sym ";")))).

  (* quasi-jessie.js.ts: block production subset. *)
  Definition block : pat :=
    seq (sym "{") (seq (star (PNT 3)) (sym "}")).

  Definition grammar : Syntax.grammar :=
    [ (* 0 expr *)
      (* quasi-jessie.js.ts: assignExpr production subset. *)
      alt arrow_func
        (alt op_assign
          (alt less_than
            (alt (seq (sym "!") (PNT 0)) (* !expr *)
              (seq (PNT 1) (star expr_post_op)))));
      (* 1 primaryExpr *)
      (* quasi-jessie.js.ts: primaryExpr inherits Justin primaryExpr. *)
      alt string_lit
        (alt number
          (alt object_pat
            (alt paren_expr ident)));
      (* 2 propDef *)
      seq (alt ident number) (seq (sym ":") (PNT 0));
      (* 3 statement *)
      (* quasi-jessie.js.ts: binding / import / if / throw / exprStatement / declOp subset. *)
      alt if_stmt
        (alt import_stmt
          (alt throw_stmt
            (alt const_decl
              (alt let_decl
                (alt return_stmt
                  (alt assert_stmt expr_stmt))))));
      (* 4 block / arrow body block *)
      block;
      (* 5 module body *)
      (* quasi-jessie.js.ts: start production subset. *)
      seq ws (seq (star (PNT 3)) (seq ws eof))
    ].

  Definition expr : pat := PNT 0.
  Definition statement : pat := PNT 3.
  Definition moduleBody : pat := PNT 5.
  Definition exact_module_source (src : string) : pat :=
    seq ws (seq (string_pat src) (seq ws eof)).

  Example parse_op_assign :
    matches_comp grammar expr "count += 1" 512 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_arrow_expr :
    matches_comp grammar expr "() => (count += 1)" 1024 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  (* TDD RED: string literal parsing - should fail because string_lit not in grammar *)
  Example parse_string_lit_single :
    matches_comp grammar expr "'hello'" 512 = Some (Success "").
  Proof. vm_compute. reflexivity. Qed.

  (* TDD RED: import statement - should fail because import_stmt not in grammar *)
  Example parse_import_stmt :
    matches_comp grammar statement "import { E } from '@endo/far';" 1024 = Some (Success "").
  Proof. vm_compute. reflexivity. Qed.

  (* TDD RED: throw statement - should fail because throw_stmt not in grammar *)
  Example parse_throw_stmt :
    matches_comp grammar statement "throw Error('join failed');" 1024 = Some (Success "").
  Proof. vm_compute. reflexivity. Qed.

  (* TDD RED: ! prefix operator - should fail because prefix ! not in grammar *)
  Example parse_prefix_not :
    matches_comp grammar expr "!true" 512 = Some (Success "").
  Proof. vm_compute. reflexivity. Qed.

  (* TDD RED: if statement - should fail because if_stmt not in grammar *)
  Example parse_if_stmt :
    matches_comp grammar statement "if (true) { }" 1024 = Some (Success "").
  Proof. vm_compute. reflexivity. Qed.

  (* TDD RED: escrow2013 uses arrow functions with named parameters. *)
  Example parse_arrow_params :
    matches_comp grammar expr "(p1, p2) => p1" 1024 = Some (Success "").
  Proof. vm_compute. reflexivity. Qed.

  Definition run_pat (g : Syntax.grammar) (p : pat) (fuel : nat) (s : string)
      : option string :=
    match matches_comp g p s fuel with
    | Some (Success rest) => Some rest
    | _ => None
    end.

  Definition run_lex (p : pat) (fuel : nat) (s : string) : option string :=
    run_pat [] p fuel s.

  Fixpoint string_chars (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String c s' => c :: string_chars s'
    end.

  Definition string_of_ascii_list (xs : list ascii) : string :=
    fold_right String EmptyString xs.

  Fixpoint ascii_list_eqb (xs ys : list ascii) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => Ascii.eqb x y && ascii_list_eqb xs' ys'
    | _, _ => false
    end.

  Definition is_space (c : ascii) : bool :=
    orb (Ascii.eqb c " "%char)
      (orb (Ascii.eqb c "009"%char)
         (orb (Ascii.eqb c "010"%char)
            (Ascii.eqb c "013"%char))).

  Fixpoint drop_leading_ws (xs : list ascii) : list ascii :=
    match xs with
    | c :: rest => if is_space c then drop_leading_ws rest else xs
    | [] => []
    end.

  Definition trim_right_ws (s : string) : string :=
    string_of_ascii_list (rev (drop_leading_ws (rev (string_chars s)))).

  Definition consumed_fragment (s rest : string) : option string :=
    let xs := string_chars s in
    let ys := string_chars rest in
    let n := Nat.sub (List.length xs) (List.length ys) in
    if ascii_list_eqb ys (skipn n xs)
    then Some (string_of_ascii_list (firstn n xs))
    else None.

  Definition expect_sym_tok (tok : string) (fuel : nat) (s : string)
      : option string :=
    run_lex (sym tok) fuel s.

  Definition expect_kw_tok (tok : string) (fuel : nat) (s : string)
      : option string :=
    run_lex (kw tok) fuel s.

  Definition char_digit_value (c : ascii) : option nat :=
    if Ascii.eqb c "0"%char then Some 0%nat else
    if Ascii.eqb c "1"%char then Some 1%nat else
    if Ascii.eqb c "2"%char then Some 2%nat else
    if Ascii.eqb c "3"%char then Some 3%nat else
    if Ascii.eqb c "4"%char then Some 4%nat else
    if Ascii.eqb c "5"%char then Some 5%nat else
    if Ascii.eqb c "6"%char then Some 6%nat else
    if Ascii.eqb c "7"%char then Some 7%nat else
    if Ascii.eqb c "8"%char then Some 8%nat else
    if Ascii.eqb c "9"%char then Some 9%nat else
    None.

  Fixpoint digits_to_nat (acc : nat) (xs : list ascii) : option nat :=
    match xs with
    | [] => Some acc
    | c :: rest =>
        match char_digit_value c with
        | Some d => digits_to_nat (10 * acc + d)%nat rest
        | None => None
        end
    end.

  Definition unsigned_Z_of_string (s : string) : option Z :=
    match string_chars s with
    | [] => None
    | c :: rest =>
        match char_digit_value c with
        | Some d =>
            match digits_to_nat d rest with
            | Some n => Some (Z.of_nat n)
            | None => None
            end
        | None => None
        end
    end.

  Definition Z_of_number_token (s : string) : option Z :=
    match string_chars s with
    | "-"%char :: rest =>
        match unsigned_Z_of_string (string_of_ascii_list rest) with
        | Some n => Some (- n)
        | None => None
        end
    | _ => unsigned_Z_of_string s
    end.

  Definition parse_ident_token (fuel : nat) (s : string)
      : option (string * string) :=
    match run_lex ident fuel s with
    | Some rest =>
        match consumed_fragment s rest with
        | Some frag => Some (trim_right_ws frag, rest)
        | None => None
        end
    | None => None
    end.

  Definition parse_number_token (fuel : nat) (s : string)
      : option (Z * string) :=
    match run_lex number fuel s with
    | Some rest =>
        match consumed_fragment s rest with
        | Some frag =>
            match Z_of_number_token (trim_right_ws frag) with
            | Some n => Some (n, rest)
            | None => None
            end
        | None => None
        end
    | None => None
    end.

  Definition parse_prop_name_token (fuel : nat) (s : string)
      : option (string * string) :=
    match parse_ident_token fuel s with
    | Some ans => Some ans
    | None =>
        match run_lex number fuel s with
        | Some rest =>
            match consumed_fragment s rest with
            | Some frag => Some (trim_right_ws frag, rest)
            | None => None
            end
        | None => None
        end
    end.

  Fixpoint parse_expr_ast (fuel : nat) (s : string)
      : option (jexpr * string)
  with parse_primary_ast (fuel : nat) (s : string)
      : option (jexpr * string)
  with parse_args_ast (fuel : nat) (s : string)
      : option (list jexpr * string)
  with parse_props_ast (fuel : nat) (s : string)
      : option (list jprop * string)
  with parse_stmt_ast (fuel : nat) (s : string)
      : option (jstmt * string)
  with parse_block_stmts_ast (fuel : nat) (s : string)
      : option (list jstmt * string)
  with parse_decl_ast (fuel : nat) (s : string)
      : option (jdecl * string)
  with parse_decls_ast (fuel : nat) (s : string)
      : option (list jdecl * string).
  Proof.
    - destruct fuel as [| fuel']; [exact (@None (jexpr * string)) |].
      refine (
        match run_pat grammar arrow_func (S fuel') s with
        | Some _ =>
            match expect_sym_tok "(" (S fuel') s with
            | Some rest1 =>
                match expect_sym_tok ")" (S fuel') rest1 with
                | Some rest2 =>
                    match expect_sym_tok "=>" (S fuel') rest2 with
                    | Some rest3 =>
                        match expect_sym_tok "{" (S fuel') rest3 with
                        | Some rest4 =>
                            match parse_block_stmts_ast fuel' rest4 with
                            | Some (ss, rest5) =>
                                Some (JArrow [] (JBodyBlock ss), rest5)
                            | None => None
                            end
                        | None =>
                            match expect_sym_tok "(" (S fuel') rest3 with
                            | Some rest4 =>
                                match parse_expr_ast fuel' rest4 with
                                | Some (e, rest5) =>
                                    match expect_sym_tok ")" (S fuel') rest5 with
                                    | Some rest6 =>
                                        Some (JArrow [] (JBodyExpr e), rest6)
                                    | None => None
                                    end
                                | None => None
                                end
                            | None =>
                                match parse_expr_ast fuel' rest3 with
                                | Some (e, rest4) =>
                                    Some (JArrow [] (JBodyExpr e), rest4)
                                | None => None
                                end
                            end
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None =>
            match run_pat grammar op_assign (S fuel') s with
            | Some _ =>
                match parse_ident_token (S fuel') s with
                | Some (x, rest1) =>
                    match expect_sym_tok "+=" (S fuel') rest1 with
                    | Some rest2 =>
                        match parse_expr_ast fuel' rest2 with
                        | Some (rhs, rest3) =>
                            Some (JAssignOp "+=" (JUse x) rhs, rest3)
                        | None => None
                        end
                    | None =>
                        match expect_sym_tok "-=" (S fuel') rest1 with
                        | Some rest2 =>
                            match parse_expr_ast fuel' rest2 with
                            | Some (rhs, rest3) =>
                                Some (JAssignOp "-=" (JUse x) rhs, rest3)
                            | None => None
                            end
                        | None => None
                        end
                    end
                | None => None
                end
            | None =>
                match parse_primary_ast fuel' s with
                | Some (base, rest0) =>
                    let fix parse_post_ops (n : nat) (e : jexpr) (rest : string)
                        : option (jexpr * string) :=
                        match n with
                        | O => Some (e, rest)
                        | S n' =>
                            match expect_sym_tok "." (S fuel') rest with
                            | Some rest1 =>
                                match parse_ident_token (S fuel') rest1 with
                                | Some (field, rest2) =>
                                    parse_post_ops n' (JGet e field) rest2
                                | None => None
                                end
                            | None =>
                                match expect_sym_tok "(" (S fuel') rest with
                                | Some rest1 =>
                                    match expect_sym_tok ")" (S fuel') rest1 with
                                    | Some rest2 =>
                                        parse_post_ops n' (JCall e []) rest2
                                    | None =>
                                        match parse_args_ast fuel' rest1 with
                                        | Some (args, rest2) =>
                                            match expect_sym_tok ")" (S fuel') rest2 with
                                            | Some rest3 =>
                                                parse_post_ops n' (JCall e args) rest3
                                            | None => None
                                            end
                                        | None => None
                                        end
                                    end
                                | None => Some (e, rest)
                                end
                            end
                        end in
                    match run_pat grammar less_than (S fuel') s with
                    | Some _ =>
                        match parse_post_ops fuel' base rest0 with
                        | Some (lhs, rest1) =>
                            match expect_sym_tok "<" (S fuel') rest1 with
                            | Some rest2 =>
                                match parse_primary_ast fuel' rest2 with
                                | Some (right0, rest3) =>
                                    match parse_post_ops fuel' right0 rest3 with
                                    | Some (rhs, rest4) =>
                                        Some (JGreater rhs lhs, rest4)
                                    | None => None
                                    end
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => parse_post_ops fuel' base rest0
                    end
                | None => None
                end
            end
        end).
    - destruct fuel as [| fuel']; [exact (@None (jexpr * string)) |].
      refine (
        match parse_number_token (S fuel') s with
        | Some (n, rest) => Some (JDataNum n, rest)
        | None =>
            match run_pat grammar object_pat (S fuel') s with
            | Some _ =>
                match expect_sym_tok "{" (S fuel') s with
                | Some rest1 =>
                    match parse_props_ast fuel' rest1 with
                    | Some (props, rest2) => Some (JRecord props, rest2)
                    | None => None
                    end
                | None => None
                end
            | None =>
                match expect_sym_tok "(" (S fuel') s with
                | Some rest1 =>
                    match parse_expr_ast fuel' rest1 with
                    | Some (e, rest2) =>
                        match expect_sym_tok ")" (S fuel') rest2 with
                        | Some rest3 => Some (e, rest3)
                        | None => None
                        end
                    | None => None
                    end
                | None =>
                    match parse_ident_token (S fuel') s with
                    | Some (x, rest) => Some (JUse x, rest)
                    | None => None
                    end
                end
            end
        end).
    - destruct fuel as [| fuel']; [exact (@None (list jexpr * string)) |].
      refine (
        match parse_expr_ast fuel' s with
        | Some (e, rest1) =>
            match expect_sym_tok "," (S fuel') rest1 with
            | Some rest2 =>
                match parse_args_ast fuel' rest2 with
                | Some (args, rest3) => Some (e :: args, rest3)
                | None => None
                end
            | None => Some ([e], rest1)
            end
        | None => None
        end).
    - destruct fuel as [| fuel']; [exact (@None (list jprop * string)) |].
      refine (
        match expect_sym_tok "}" (S fuel') s with
        | Some rest => Some ([], rest)
        | None =>
            match parse_prop_name_token (S fuel') s with
            | Some (name, rest1) =>
                match expect_sym_tok ":" (S fuel') rest1 with
                | Some rest2 =>
                    match parse_expr_ast fuel' rest2 with
                    | Some (value, rest3) =>
                        match expect_sym_tok "," (S fuel') rest3 with
                        | Some rest4 =>
                            match parse_props_ast fuel' rest4 with
                            | Some (props, rest5) =>
                                Some (JProp name value :: props, rest5)
                            | None => None
                            end
                        | None =>
                            match expect_sym_tok "}" (S fuel') rest3 with
                            | Some rest4 =>
                                Some ([JProp name value], rest4)
                            | None => None
                            end
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        end).
    - destruct fuel as [| fuel']; [exact (@None (jstmt * string)) |].
      refine (
        match run_pat grammar const_decl (S fuel') s with
        | Some _ =>
            match expect_kw_tok "const" (S fuel') s with
            | Some rest1 =>
                match parse_ident_token (S fuel') rest1 with
                | Some (x, rest2) =>
                    match expect_sym_tok "=" (S fuel') rest2 with
                    | Some rest3 =>
                        match parse_expr_ast fuel' rest3 with
                        | Some (rhs, rest4) =>
                            match expect_sym_tok ";" (S fuel') rest4 with
                            | Some rest5 =>
                                Some (JConstStmt [JBind (JDef x) rhs], rest5)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None =>
            match run_pat grammar let_decl (S fuel') s with
            | Some _ =>
                match expect_kw_tok "let" (S fuel') s with
                | Some rest1 =>
                    match parse_ident_token (S fuel') rest1 with
                    | Some (x, rest2) =>
                        match expect_sym_tok "=" (S fuel') rest2 with
                        | Some rest3 =>
                            match parse_expr_ast fuel' rest3 with
                            | Some (rhs, rest4) =>
                                match expect_sym_tok ";" (S fuel') rest4 with
                                | Some rest5 =>
                                    Some (JLet [JBind (JDef x) rhs], rest5)
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None =>
                match run_pat grammar return_stmt (S fuel') s with
                | Some _ =>
                    match expect_kw_tok "return" (S fuel') s with
                    | Some rest1 =>
                        match parse_expr_ast fuel' rest1 with
                        | Some (e, rest2) =>
                            match expect_sym_tok ";" (S fuel') rest2 with
                            | Some rest3 => Some (JReturn e, rest3)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None =>
                    match run_pat grammar assert_stmt (S fuel') s with
                    | Some _ =>
                        match expect_kw_tok "assert" (S fuel') s with
                        | Some rest1 =>
                            match expect_sym_tok "(" (S fuel') rest1 with
                            | Some rest2 =>
                                match parse_expr_ast fuel' rest2 with
                                | Some (e, rest3) =>
                                    match expect_sym_tok ")" (S fuel') rest3 with
                                    | Some rest4 =>
                                        match expect_sym_tok ";" (S fuel') rest4 with
                                        | Some rest5 => Some (JAssert e, rest5)
                                        | None => None
                                        end
                                    | None => None
                                    end
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None =>
                        match run_pat grammar expr_stmt (S fuel') s with
                        | Some _ =>
                            match parse_expr_ast fuel' s with
                            | Some (e, rest1) =>
                                match expect_sym_tok ";" (S fuel') rest1 with
                                | Some rest2 => Some (JExprStmt e, rest2)
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    end
                end
            end
        end).
    - destruct fuel as [| fuel']; [exact (@None (list jstmt * string)) |].
      refine (
        match expect_sym_tok "}" (S fuel') s with
        | Some rest => Some ([], rest)
        | None =>
            match parse_stmt_ast fuel' s with
            | Some (stmt, rest1) =>
                match parse_block_stmts_ast fuel' rest1 with
                | Some (stmts, rest2) => Some (stmt :: stmts, rest2)
                | None => None
                end
            | None => None
            end
        end).
    - destruct fuel as [| fuel']; [exact (@None (jdecl * string)) |].
      refine (
        match run_pat grammar const_decl (S fuel') s with
        | Some _ =>
            match expect_kw_tok "const" (S fuel') s with
            | Some rest1 =>
                match parse_ident_token (S fuel') rest1 with
                | Some (x, rest2) =>
                    match expect_sym_tok "=" (S fuel') rest2 with
                    | Some rest3 =>
                        match parse_expr_ast fuel' rest3 with
                        | Some (rhs, rest4) =>
                            match expect_sym_tok ";" (S fuel') rest4 with
                            | Some rest5 =>
                                Some (JConst [JBind (JDef x) rhs], rest5)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end).
    - destruct fuel as [| fuel']; [exact (@None (list jdecl * string)) |].
      refine (
        match run_lex eof (S fuel') s with
        | Some rest => Some ([], rest)
        | None =>
            match parse_decl_ast fuel' s with
            | Some (decl, rest1) =>
                match parse_decls_ast fuel' rest1 with
                | Some (decls, rest2) => Some (decl :: decls, rest2)
                | None => None
                end
            | None => None
            end
        end).
  Defined.

  Definition parse_program_only (s : string) : option jmodule :=
    match run_pat grammar moduleBody 4096 s with
    | Some EmptyString =>
        match run_lex ws 256 s with
        | Some rest1 =>
            match parse_decls_ast 256 rest1 with
            | Some (decls, rest2) =>
                match run_lex ws 64 rest2 with
                | Some rest3 =>
                    match run_lex eof 64 rest3 with
                    | Some EmptyString => Some (JModule decls)
                    | _ => None
                    end
                | _ => None
                end
            | None => None
            end
        | None => None
        end
    | _ => None
    end.

  (** Parser tests *)

  (* Test 1: Can a module start with whitespace? *)
  Example test_whitespace_prefix :
    matches_comp grammar moduleBody " const x = 1;" 512 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  (* Test 2: Does the parser accept property names starting with underscore? *)
  Example test_underscore_property :
    matches_comp grammar moduleBody "const obj = { _fst: 1 };" 512 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  (* Test 3: Does assert work? *)
  Example test_assert_statement :
    matches_comp grammar moduleBody "const f = () => { assert(true); };" 1024 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  (* Test 4: Complex function with nested blocks *)
  Example test_nested_function :
    matches_comp grammar moduleBody "const f = () => { const g = () => 2; };" 1024 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Definition checkedCounter_source : string :=
    "const checkedCounter = () => {
  const c = makeCounter();
  const cUp = { incr: c.incr };
  const use = () => {
    assert(0 < c.incr());
  };
  return { _fst: use, _snd: cUp };
};".

  Definition checkedCounter_jessica_program : jmodule :=
    JModule
      [JConst
        [JBind
          (JDef "checkedCounter")
          (JArrow []
            (JBodyBlock
              [JConstStmt [JBind (JDef "c") (JCall (JUse "makeCounter") [])];
               JConstStmt
                 [JBind (JDef "cUp")
                   (JRecord [JProp "incr" (JGet (JUse "c") "incr")])];
               JConstStmt
                 [JBind (JDef "use")
                   (JArrow []
                     (JBodyBlock
                       [JAssert
                         (JGreater
                           (JCall (JGet (JUse "c") "incr") [])
                           (JDataNum 0))]))];
               JReturn
                 (JRecord
                   [JProp "_fst" (JUse "use");
                    JProp "_snd" (JUse "cUp")])]))]].

  Example parse_checkedCounter_source_program :
    parse_program_only checkedCounter_source = Some checkedCounter_jessica_program.
  Proof. vm_compute. reflexivity. Qed.

End QuasiJessie.
