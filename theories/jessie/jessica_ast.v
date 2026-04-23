From Coq Require Import List String ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module JessicaAst.
  Inductive jpat :=
  | JDef (x : string)
  | JMatchArray (ps : list jpat).

  Inductive jimport_bind :=
  | JImportAs (local imported : string).

  Inductive jexpr :=
  | JUse (x : string)
  | JDataNum (n : Z)
  | JDataString (s : string)
  | JArray (xs : list jexpr)
  (* TODO: consider whether the lhs of JAssignOp should be a narrower pattern
     or l-value category rather than a full expression. *)
  | JAssignOp (op : string) (lhs rhs : jexpr)
  | JAssign (lhs rhs : jexpr)
  | JGet (obj : jexpr) (field : string)
  | JCall (callee : jexpr) (args : list jexpr)
  | JGreater (lhs rhs : jexpr)
  | JPreOp (op : string) (arg : jexpr)
  | JRecord (fields : list jprop)
  | JArrow (params : list jpat) (body : jbody)
  | JLambda (params : list jpat) (body : jbody)
  with jprop :=
  | JProp (name : string) (value : jexpr)
  with jbody :=
  | JBodyExpr (e : jexpr)
  | JBodyBlock (ss : list jstmt)
  with jstmt :=
  | JConstStmt (bindings : list jbind)
  | JLet (bindings : list jbind)
  | JLetNames (names : list jpat)
  | JExprStmt (e : jexpr)
  | JAssert (e : jexpr)
  | JIf (cond : jexpr) (then_branch : list jstmt) (else_branch : option (list jstmt))
  | JThrow (e : jexpr)
  | JReturn (e : jexpr)
  with jbind :=
  | JBind (lhs : jpat) (rhs : jexpr).

  Inductive jdecl :=
  | JImport (bindings : list jimport_bind) (from : string)
  | JConst (bindings : list jbind).

  Inductive jmodule :=
  | JModule (decls : list jdecl).
End JessicaAst.
