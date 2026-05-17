From Coq Require Import Lists.List Strings.Ascii Strings.String ZArith.
From Peg Require Import Charset Syntax Match.
From iris.jessie Require Import jessica_ast quasi_json quasi_justin.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(*
  Jessie PEG grammar, mirroring the TypeScript PEG at:

    https://github.com/endojs/Jessie/blob/main/packages/parse/src/quasi-jessie.js.ts

  Each Coq rule corresponds to a production in that file.  The non-terminal
  indices (PNT n) map directly to the grammar list at the bottom of this module.

  Notation:
    a >> b   — sequence  (PEG adjacency)
    a /// b  — choice    (PEG /)
*)

Module JessiePegNotation.
  Notation "p >> q" := (PSequence p q)
    (at level 69, right associativity).
  Notation "p /// q" := (PChoice p q)
    (at level 60, right associativity).
End JessiePegNotation.

Import JessiePegNotation.

Module QuasiJessie.
  Import JessicaAst.
  Import QuasiJson.
  Import QuasiJustin.

  (* ── Punctuation aliases ──────────────────────────────────────── *)
  Definition LEFT_BRACE  : pat := sym "{".
  Definition RIGHT_BRACE : pat := sym "}".
  Definition LEFT_BRACKET  : pat := sym "[".
  Definition RIGHT_BRACKET : pat := sym "]".
  Definition LPAREN : pat := sym "(".
  Definition RPAREN : pat := sym ")".
  Definition COMMA  : pat := sym ",".
  Definition SEMI   : pat := sym ";".
  Definition COLON  : pat := sym ":".
  Definition DOT    : pat := sym ".".
  Definition ARROW  : pat := sym "=>".
  Definition BANG   : pat := sym "!".
  Definition ASSIGN : pat := sym "=".
  Definition PLUS_ASSIGN  : pat := sym "+=".
  Definition MINUS_ASSIGN : pat := sym "-=".
  Definition LESS_THAN    : pat := sym "<".

  (* ══════════════════════════════════════════════════════════════════
     Lexical rules
     ══════════════════════════════════════════════════════════════════ *)

  (* ── String literals ──────────────────────────────────────────── *)
  (* quasi-jessie.js.ts: stringLitSngl <- SQUOTE ... SQUOTE;
     TODO: No escape handling in this subset.
     Definition lives in QuasiJustin, imported above. *)

  (* ══════════════════════════════════════════════════════════════════
     Expressions
     ══════════════════════════════════════════════════════════════════ *)

  (* ── L-value ──────────────────────────────────────────────────── *)
  (* quasi-jessie.js.ts: lValue <- ... ; narrowed to identifiers only. *)
  Definition lvalue : pat := ident.

  (* quasi-jessie.js.ts: opAssign <- lValue OP_ASSIGN assignExpr *)
  Definition op_assign : pat :=
    lvalue >> (PLUS_ASSIGN /// MINUS_ASSIGN) >> PNT 0.

  (* quasi-jessie.js.ts: assignExpr <- lValue EQ assignExpr *)
  Definition assign_expr : pat :=
    lvalue >> ASSIGN >> PNT 0.

  Definition paren_expr : pat :=
    LPAREN >> PNT 0 >> RPAREN.

  (* ── Record / object literal ──────────────────────────────────── *)
  (* quasi-jessie.js.ts: record <- LEFT_BRACE propDef ** _COMMA _COMMA? RIGHT_BRACE *)
  Definition record : pat :=
    LEFT_BRACE >> opt (PNT 2 >> star (COMMA >> PNT 2) >> opt COMMA) >> RIGHT_BRACE.

  (* ── Array literal ────────────────────────────────────────────── *)
  Definition comma_list (elem : pat) : pat :=
    elem >> star (COMMA >> elem).

  Definition array_pat : pat :=
    LEFT_BRACKET >> opt (comma_list (PNT 0) >> opt COMMA) >> RIGHT_BRACKET.

  (* ── Arrow function ───────────────────────────────────────────── *)
  Definition match_array_param : pat :=
    LEFT_BRACKET >> opt (comma_list ident) >> RIGHT_BRACKET.

  Definition arrow_param : pat := match_array_param /// ident.

  Definition arrow_params : pat :=
    ident /// (LPAREN >> opt (comma_list arrow_param) >> RPAREN).

  Definition arrow_body : pat :=
    PNT 4 /// paren_expr /// PNT 0.

  (* quasi-jessie.js.ts:
     arrowFunc <- arrowParams _NO_NEWLINE ARROW block
                / arrowParams _NO_NEWLINE ARROW assignExpr; *)
  Definition arrow_func : pat :=
    arrow_params >> ARROW >> arrow_body.

  (* ── Postfix operations ───────────────────────────────────────── *)
  (* quasi-jessie.js.ts:
     memberPostOp / callPostOp extensions inherited from Justin. *)
  Definition expr_post_op : pat := QuasiJustin.post_op 0.

  (* ── Comparison ───────────────────────────────────────────────── *)
  Definition less_than : pat :=
    PNT 1 >> star expr_post_op >> LESS_THAN
         >> PNT 1 >> star expr_post_op.

  (* ══════════════════════════════════════════════════════════════════
     Declarations
     ══════════════════════════════════════════════════════════════════ *)

  Definition const_decl : pat :=
    kw "const" >> ident >> ASSIGN >> PNT 0 >> SEMI.

  Definition let_decl : pat :=
    kw "let" >> ident >> opt (ASSIGN >> PNT 0) >> SEMI.

  (* quasi-jessie.js.ts: importDeclaration *)
  Definition import_stmt : pat :=
    kw "import" >> LEFT_BRACE >> ident >> RIGHT_BRACE
                >> kw "from" >> string_lit >> SEMI.

  (* ══════════════════════════════════════════════════════════════════
     Statements
     ══════════════════════════════════════════════════════════════════ *)

  (* quasi-jessie.js.ts: returnStatement production subset. *)
  Definition return_stmt : pat :=
    kw "return" >> PNT 0 >> SEMI.

  Definition throw_stmt : pat :=
    kw "throw" >> PNT 0 >> SEMI.

  (* quasi-jessie.js.ts: ifStatement *)
  Definition if_stmt : pat :=
    kw "if" >> LPAREN >> PNT 0 >> RPAREN
         >> PNT 4
         >> opt (kw "else" >> PNT 4).

  (* quasi-jessie.js.ts: exprStatement <- ~cantStartExprStatement expr SEMI. *)
  Definition expr_stmt : pat := PNT 0 >> SEMI.

  Definition assert_stmt : pat :=
    kw "assert" >> LPAREN >> PNT 0 >> RPAREN >> SEMI.

  (* quasi-jessie.js.ts: block production subset. *)
  Definition block : pat :=
    LEFT_BRACE >> star (PNT 3) >> RIGHT_BRACE.

  (* ══════════════════════════════════════════════════════════════════
     Grammar (indexed productions, referenced by PNT n)
     ══════════════════════════════════════════════════════════════════ *)
  Definition grammar : Syntax.grammar :=
    [ (* 0 expr — quasi-jessie.js.ts: assignExpr production subset *)
      arrow_func
      /// op_assign
      /// assign_expr
      /// less_than
      /// (BANG >> PNT 0)
      /// (PNT 1 >> star expr_post_op);
      (* 1 primaryExpr — quasi-jessie.js.ts: primaryExpr inherits Justin *)
      string_lit
      /// number
      /// array_pat
      /// record
      /// paren_expr
      /// ident;
      (* 2 propDef *)
      (ident /// number) >> COLON >> PNT 0;
      (* 3 statement — quasi-jessie.js.ts: binding/import/if/throw/exprStatement/declOp *)
      if_stmt
      /// import_stmt
      /// throw_stmt
      /// const_decl
      /// let_decl
      /// return_stmt
      /// assert_stmt
      /// expr_stmt;
      (* 4 block / arrow body block *)
      block;
      (* 5 module body — quasi-jessie.js.ts: start production subset *)
      ws >> star (PNT 3) >> ws >> eof
    ].

  Definition expr : pat := PNT 0.
  Definition statement : pat := PNT 3.
  Definition moduleBody : pat := PNT 5.
  Definition exact_module_source (src : string) : pat :=
    ws >> string_pat src >> ws >> eof.

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

  Fixpoint parse_string_lit_content (fuel : nat) (s : string)
      : option (string * string) :=
    match fuel with
    | O => None
    | S fuel' =>
        match s with
        | EmptyString => None
        | String c s' =>
            if Ascii.eqb c "'"%char then Some (EmptyString, s')
            else
              match parse_string_lit_content fuel' s' with
              | Some (cs, rest) => Some (String c cs, rest)
              | None => None
              end
        end
    end.

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

  Definition parse_string_lit_token (fuel : nat) (s : string)
      : option (string * string) :=
    match expect_sym_tok "'" fuel s with
    | Some rest1 =>
        match parse_string_lit_content fuel rest1 with
        | Some (content, rest2) =>
            match run_lex ws fuel rest2 with
            | Some rest3 => Some (content, rest3)
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

  Fixpoint parse_arrow_params_after_open (fuel : nat) (s : string)
      : option (list jpat * string)
  with parse_match_array_params_after_open (fuel : nat) (s : string)
      : option (list jpat * string)
  with parse_arrow_param_ast (fuel : nat) (s : string)
      : option (jpat * string).
  Proof.
  - destruct fuel as [| fuel']; [exact (@None (list jpat * string)) |].
    refine (
      match expect_sym_tok ")" (S fuel') s with
      | Some rest => Some ([], rest)
      | None =>
          match parse_arrow_param_ast fuel' s with
          | Some (p, rest1) =>
              match expect_sym_tok "," (S fuel') rest1 with
              | Some rest2 =>
                  match parse_arrow_params_after_open fuel' rest2 with
                  | Some (ps, rest3) => Some (p :: ps, rest3)
                  | None => None
                  end
              | None =>
                  match expect_sym_tok ")" (S fuel') rest1 with
                  | Some rest2 => Some ([p], rest2)
                  | None => None
                  end
              end
          | None => None
          end
      end).
  - destruct fuel as [| fuel']; [exact (@None (list jpat * string)) |].
    refine (
      match expect_sym_tok "]" (S fuel') s with
      | Some rest => Some ([], rest)
      | None =>
          match parse_arrow_param_ast fuel' s with
          | Some (p, rest1) =>
              match expect_sym_tok "," (S fuel') rest1 with
              | Some rest2 =>
                  match parse_match_array_params_after_open fuel' rest2 with
                  | Some (ps, rest3) => Some (p :: ps, rest3)
                  | None => None
                  end
              | None =>
                  match expect_sym_tok "]" (S fuel') rest1 with
                  | Some rest2 => Some ([p], rest2)
                  | None => None
                  end
              end
          | None => None
          end
      end).
  - destruct fuel as [| fuel']; [exact (@None (jpat * string)) |].
    refine (
      match expect_sym_tok "[" (S fuel') s with
      | Some rest1 =>
          match parse_match_array_params_after_open fuel' rest1 with
          | Some (ps, rest2) => Some (JMatchArray ps, rest2)
          | None => None
          end
      | None =>
          match parse_ident_token (S fuel') s with
          | Some (x, rest) => Some (JDef x, rest)
          | None => None
          end
      end).
  Defined.

  Definition parse_arrow_params_ast (fuel : nat) (s : string)
      : option (list jpat * string) :=
    match parse_ident_token fuel s with
    | Some (x, rest) => Some ([JDef x], rest)
    | None =>
        match expect_sym_tok "(" fuel s with
        | Some rest => parse_arrow_params_after_open fuel rest
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
            match parse_arrow_params_ast (S fuel') s with
            | Some (params, rest2) =>
                match expect_sym_tok "=>" (S fuel') rest2 with
                    | Some rest3 =>
                        match expect_sym_tok "{" (S fuel') rest3 with
                        | Some rest4 =>
                            match parse_block_stmts_ast fuel' rest4 with
                            | Some (ss, rest5) =>
                                Some (JArrow params (JBodyBlock ss), rest5)
                            | None => None
                            end
                        | None =>
                            match expect_sym_tok "(" (S fuel') rest3 with
                            | Some rest4 =>
                                match parse_expr_ast fuel' rest4 with
                                | Some (e, rest5) =>
                                    match expect_sym_tok ")" (S fuel') rest5 with
                                    | Some rest6 =>
                                        Some (JArrow params (JBodyExpr e), rest6)
                                    | None => None
                                    end
                                | None => None
                                end
                            | None =>
                                match parse_expr_ast fuel' rest3 with
                                | Some (e, rest4) =>
                                    Some (JArrow params (JBodyExpr e), rest4)
                                | None => None
                                end
                            end
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
                match run_pat grammar assign_expr (S fuel') s with
                | Some _ =>
                    match parse_ident_token (S fuel') s with
                    | Some (x, rest1) =>
                        match expect_sym_tok "=" (S fuel') rest1 with
                        | Some rest2 =>
                            match parse_expr_ast fuel' rest2 with
                            | Some (rhs, rest3) =>
                                Some (JAssign (JUse x) rhs, rest3)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None =>
                match expect_sym_tok "!" (S fuel') s with
                | Some rest1 =>
                    match parse_expr_ast fuel' rest1 with
                    | Some (e, rest2) => Some (JPreOp "!" e, rest2)
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
                end
            end
        end).
    - destruct fuel as [| fuel']; [exact (@None (jexpr * string)) |].
      refine (
        match parse_string_lit_token (S fuel') s with
        | Some (lit, rest) => Some (JDataString lit, rest)
        | None =>
        match parse_number_token (S fuel') s with
        | Some (n, rest) => Some (JDataNum n, rest)
        | None =>
            match run_pat grammar array_pat (S fuel') s with
            | Some _ =>
                match expect_sym_tok "[" (S fuel') s with
                | Some rest1 =>
                    let fix parse_array_elems_after_open (n : nat) (rest : string)
                        : option (list jexpr * string) :=
                        match n with
                        | O => None
                        | S n' =>
                            match expect_sym_tok "]" (S fuel') rest with
                            | Some rest2 => Some ([], rest2)
                            | None =>
                                match parse_expr_ast n' rest with
                                | Some (e, rest2) =>
                                    match expect_sym_tok "," (S fuel') rest2 with
                                    | Some rest3 =>
                                        match parse_array_elems_after_open n' rest3 with
                                        | Some (es, rest4) => Some (e :: es, rest4)
                                        | None => None
                                        end
                                    | None =>
                                        match expect_sym_tok "]" (S fuel') rest2 with
                                        | Some rest3 => Some ([e], rest3)
                                        | None => None
                                        end
                                    end
                                | None => None
                                end
                            end
                        end in
                    match parse_array_elems_after_open fuel' rest1 with
                    | Some (es, rest2) => Some (JArray es, rest2)
                    | None => None
                    end
                | None => None
                end
            | None =>
            match run_pat grammar record (S fuel') s with
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
        match run_pat grammar if_stmt (S fuel') s with
        | Some _ =>
            match expect_kw_tok "if" (S fuel') s with
            | Some rest1 =>
                match expect_sym_tok "(" (S fuel') rest1 with
                | Some rest2 =>
                    match parse_expr_ast fuel' rest2 with
                    | Some (cond, rest3) =>
                        match expect_sym_tok ")" (S fuel') rest3 with
                        | Some rest4 =>
                            match expect_sym_tok "{" (S fuel') rest4 with
                            | Some rest5 =>
                                match parse_block_stmts_ast fuel' rest5 with
                                | Some (then_branch, rest6) =>
                                    match expect_kw_tok "else" (S fuel') rest6 with
                                    | Some rest7 =>
                                        match expect_sym_tok "{" (S fuel') rest7 with
                                        | Some rest8 =>
                                            match parse_block_stmts_ast fuel' rest8 with
                                            | Some (else_branch, rest9) =>
                                                Some (JIf cond then_branch (Some else_branch), rest9)
                                            | None => None
                                            end
                                        | None => None
                                        end
                                    | None => Some (JIf cond then_branch None, rest6)
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
                end
            | None => None
            end
        | None =>
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
                          | None =>
                              match expect_sym_tok ";" (S fuel') rest2 with
                              | Some rest3 => Some (JLetNames [JDef x], rest3)
                              | None => None
                              end
                          end
                    | None => None
                    end
                | None => None
                end
            | None =>
                match run_pat grammar throw_stmt (S fuel') s with
                | Some _ =>
                    match expect_kw_tok "throw" (S fuel') s with
                    | Some rest1 =>
                        match parse_expr_ast fuel' rest1 with
                        | Some (e, rest2) =>
                            match expect_sym_tok ";" (S fuel') rest2 with
                            | Some rest3 => Some (JThrow e, rest3)
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
        match run_pat grammar import_stmt (S fuel') s with
        | Some _ =>
            match expect_kw_tok "import" (S fuel') s with
            | Some rest1 =>
                match expect_sym_tok "{" (S fuel') rest1 with
                | Some rest2 =>
                    match parse_ident_token (S fuel') rest2 with
                    | Some (x, rest3) =>
                        match expect_sym_tok "}" (S fuel') rest3 with
                        | Some rest4 =>
                            match expect_kw_tok "from" (S fuel') rest4 with
                            | Some rest5 =>
                                match parse_string_lit_token (S fuel') rest5 with
                                | Some (from, rest6) =>
                                    match expect_sym_tok ";" (S fuel') rest6 with
                                    | Some rest7 =>
                                        Some (JImport [JImportAs x x] from, rest7)
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
                end
            | None => None
            end
        | None =>
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
        end
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

  Example parse_arrow_params_program :
    parse_program_only "const f = (p1, p2) => p1;" =
      Some (JModule
        [JConst
          [JBind
            (JDef "f")
            (JArrow [JDef "p1"; JDef "p2"] (JBodyExpr (JUse "p1")))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_import_program :
    parse_program_only "import { E } from '@endo/far';" =
      Some (JModule [JImport [JImportAs "E" "E"] "@endo/far"]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_string_lit_program :
    parse_program_only "const message = 'join failed';" =
      Some (JModule
        [JConst [JBind (JDef "message") (JDataString "join failed")]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_array_program :
    parse_program_only "const xs = [p1, p2];" =
      Some (JModule
        [JConst [JBind (JDef "xs") (JArray [JUse "p1"; JUse "p2"])]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_array_trailing_comma_program :
    parse_program_only "const xs = [p1, p2,];" =
      Some (JModule
        [JConst [JBind (JDef "xs") (JArray [JUse "p1"; JUse "p2"])]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_bare_arrow_param_program :
    parse_program_only "const f = x => x;" =
      Some (JModule
        [JConst [JBind (JDef "f") (JArrow [JDef "x"] (JBodyExpr (JUse "x")))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_array_pattern_arrow_param_program :
    parse_program_only "const f = ([r1, r2]) => r1;" =
      Some (JModule
        [JConst
          [JBind
            (JDef "f")
            (JArrow
              [JMatchArray [JDef "r1"; JDef "r2"]]
              (JBodyExpr (JUse "r1")))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_prefix_not_program :
    parse_program_only "const negated = !ok;" =
      Some (JModule
        [JConst [JBind (JDef "negated") (JPreOp "!" (JUse "ok"))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_if_program :
    parse_program_only "const f = () => { if (ok) { return ok; } };" =
      Some (JModule
        [JConst
          [JBind
            (JDef "f")
            (JArrow []
              (JBodyBlock
                [JIf (JUse "ok") [JReturn (JUse "ok")] None]))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_throw_program :
    parse_program_only "const f = () => { throw Error('join failed'); };" =
      Some (JModule
        [JConst
          [JBind
            (JDef "f")
            (JArrow []
              (JBodyBlock
                [JThrow
                  (JCall (JUse "Error") [JDataString "join failed"])]))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_assign_program :
    parse_program_only "const f = () => { decide = resolve; };" =
      Some (JModule
        [JConst
          [JBind
            (JDef "f")
            (JArrow []
              (JBodyBlock
                [JExprStmt (JAssign (JUse "decide") (JUse "resolve"))]))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_let_name_program :
    parse_program_only "const f = () => { let decide; };" =
      Some (JModule
        [JConst
          [JBind
            (JDef "f")
            (JArrow [] (JBodyBlock [JLetNames [JDef "decide"]]))]]).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_line_comment_program :
    parse_program_only "const x = 1; // phase 1
" =
      Some (JModule [JConst [JBind (JDef "x") (JDataNum 1)]]).
  Proof. vm_compute. reflexivity. Qed.

End QuasiJessie.
