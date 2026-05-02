From Coq Require Import List String ZArith.
From iris.heap_lang Require Import lang notation.
From iris.heap_lang.lib Require Import abort.
From iris.jessie Require Import jessie_notation jessica_ast.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module JessicaToHla.
  Import JessicaAst.

  Definition pat_name (p : jpat) : option string :=
    match p with
    | JDef x => Some x
    | _ => None
    end.

  Definition op_of_string (op : string) : option bin_op :=
    if String.eqb op "+=" then Some PlusOp else
    if String.eqb op "-=" then Some MinusOp else
    None.

  Fixpoint option_all {A} (xs : list (option A)) : option (list A) :=
    match xs with
    | [] => Some []
    | Some x :: xs' =>
        match option_all xs' with
        | Some ys => Some (x :: ys)
        | None => None
        end
    | None :: _ => None
    end.

  Fixpoint jessica_expr_to_hla (env : list string) (e : jexpr) : option heap_lang.expr
  with jessica_prop_to_hla (env : list string) (p : jprop) : option (string * heap_lang.expr)
  with jessica_body_to_hla (env : list string) (body : jbody) : option heap_lang.expr.
  Proof.
    - destruct e as [x|n|s|xs|op lhs rhs|lhs rhs|obj field|callee args|lhs rhs|op arg|fields|params body|params body].
      + exact (Some (Var x)).
      + exact (Some (Lit (LitInt n))).
      + exact (Some (of_val (j_string s))).
      + exact (
          match option_all (map (jessica_expr_to_hla env) xs) with
          | Some es => Some (fold_right (fun e acc => Pair e acc) Unit es)
          | None => None
          end).
      + exact (
          match op_of_string op, lhs, jessica_expr_to_hla env rhs with
          | Some bop, JUse x, Some rhs1 => Some (op_assign bop (Var x) rhs1)
          | _, _, _ => None
          end).
      + exact (
          match lhs with
          | JUse x =>
              match jessica_expr_to_hla env rhs with
              | Some rhs1 => Some (App (Lam BAnon (Var x)) (Store (Var x) rhs1))
              | None => None
              end
          | _ => None
          end).
      + exact (
          match jessica_expr_to_hla env obj with
          | Some obj1 => Some (obj_get obj1 (j_string field))
          | None => None
          end).
      + exact (
          match jessica_expr_to_hla env callee, option_all (map (jessica_expr_to_hla env) args) with
          | Some callee1, Some args1 =>
              Some (fold_left (fun acc arg => App acc arg) args1 callee1)
          | _, _ => None
          end).
      + exact (
          match jessica_expr_to_hla env lhs, jessica_expr_to_hla env rhs with
          | Some lhs1, Some rhs1 => Some (BinOp LtOp rhs1 lhs1)
          | _, _ => None
          end).
      + exact (
          match op, jessica_expr_to_hla env arg with
          | "!", Some arg1 => Some (UnOp NegOp arg1)
          | _, _ => None
          end).
      + exact (
          match option_all (map (jessica_prop_to_hla env) fields) with
          | Some kvs => Some (j_object kvs)
          | None => None
          end).
      + exact (
          match option_all (map pat_name params) with
          | Some xs =>
              match jessica_body_to_hla ((rev xs ++ env)%list) body with
              | Some body1 =>
                  let arrow_body :=
                    match xs with
                    | [] => Lam BAnon body1
                    | x :: xs' =>
                        Lam (BNamed x)
                          (fold_right (fun y acc => Lam (BNamed y) acc) body1 xs')
                    end in
                  Some (fold_right (fun x acc => App (Lam (BNamed x) acc) (Var x)) arrow_body env)
              | None => None
              end
          | None => None
          end).
      + exact (
          match option_all (map pat_name params) with
          | Some xs =>
              match jessica_body_to_hla ((rev xs ++ env)%list) body with
              | Some body1 =>
                  let lam_body :=
                    match xs with
                    | [] => Lam BAnon body1
                    | x :: xs' =>
                        Lam (BNamed x) (fold_right (fun y acc => Lam (BNamed y) acc) body1 xs')
                    end in
                  Some (fold_right (fun x acc => App (Lam (BNamed x) acc) (Var x)) lam_body env)
              | None => None
              end
          | None => None
          end).
    - destruct p as [name value].
      exact (
        match jessica_expr_to_hla env value with
        | Some value1 => Some (name, value1)
        | None => None
        end).
    - destruct body as [e|ss].
      + exact (jessica_expr_to_hla env e).
      + refine (
          let fix compile_stmt_list (env0 : list string) (ss0 : list jstmt) {struct ss0}
              : option heap_lang.expr :=
              let fix compile_bindings (alloc : bool) (env1 : list string) (bs : list jbind)
                  (k : list string -> option heap_lang.expr) {struct bs}
                  : option heap_lang.expr :=
                  match bs with
                  | [] => k env1
                  | JBind lhs rhs :: bs'' =>
                      match pat_name lhs, jessica_expr_to_hla env1 rhs with
                      | Some x, Some rhs1 =>
                          match compile_bindings alloc (x :: env1) bs'' k with
                          | Some rest =>
                              if alloc
                              then Some (Let (BNamed x) (Alloc rhs1) rest)
                              else Some (Let (BNamed x) rhs1 rest)
                          | None => None
                          end
                      | _, _ => None
                      end
                  end in
              match ss0 with
              | [] => Some Unit
              | s0 :: ss' =>
                  match s0 with
                  | JConstStmt bs =>
                      compile_bindings false env0 bs (fun env' => compile_stmt_list env' ss')
                  | JLet bs =>
                      compile_bindings true env0 bs (fun env' => compile_stmt_list env' ss')
                  | JLetNames names =>
                      match option_all (map pat_name names) with
                      | Some xs =>
                          match compile_stmt_list (rev xs ++ env0)%list ss' with
                          | Some rest =>
                              Some (fold_right (fun x acc => Let (BNamed x) Unit acc) rest xs)
                          | None => None
                          end
                      | None => None
                      end
                  | JExprStmt e0 =>
                      match jessica_expr_to_hla env0 e0, compile_stmt_list env0 ss' with
                      | Some e1, Some rest => Some (Let BAnon e1 rest)
                      | _, _ => None
                      end
                  | JAssert e0 =>
                      match jessica_expr_to_hla env0 e0, compile_stmt_list env0 ss' with
                      | Some e1, Some rest => Some (Let BAnon (Assert e1) rest)
                      | _, _ => None
                      end
                  | JIf _ _ _ => None
                  | JThrow e0 =>
                      match jessica_expr_to_hla env0 e0 with
                      | Some e1 => Some (Let BAnon e1 abort)
                      | None => None
                      end
                  | JReturn e0 =>
                      match ss' with
                      | [] => jessica_expr_to_hla env0 e0
                      | _ => Some Unit
                      end
                  end
              end in
          compile_stmt_list env ss).
  Defined.

  Fixpoint jessica_decls_to_hla (env : list string) (ds : list jdecl) : option heap_lang.expr :=
    match ds with
    | [] => Some Unit
    | JImport _ _ :: _ => None
    | JConst bs :: ds' =>
        let fix compile_bindings (env0 : list string) (bs0 : list jbind)
            (k : list string -> option heap_lang.expr) {struct bs0}
            : option heap_lang.expr :=
            match bs0 with
            | [] => k env0
            | JBind lhs rhs :: bs1 =>
                match pat_name lhs, jessica_expr_to_hla env0 rhs with
                | Some x, Some rhs1 =>
                    match compile_bindings (x :: env0) bs1 k with
                    | Some rest => Some (Let (BNamed x) rhs1 rest)
                    | None => None
                    end
                | _, _ => None
                end
            end in
        compile_bindings env bs (fun env' => jessica_decls_to_hla env' ds')
    end.

  Definition jessica_to_hla_module (m : jmodule) : option heap_lang.expr :=
    match m with
    | JModule ds => jessica_decls_to_hla [] ds
    end.
End JessicaToHla.
