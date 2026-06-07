import CppFormalization.Cpp3.Effects.Footprint
import CppFormalization.Cpp3.Static.WellFormed

/-!
# CppFormalization.Cpp3.Effects.Syntax

Syntax-directed effect observations.

These predicates only record which source names are mentioned by an access and
which syntax shapes may require dereference-like runtime support.  They do not
say that the mentioned names resolve, that a pointer is live, or that a write is
safe for a later program point.
-/

namespace Cpp3
namespace Effects

mutual

/-- Names consulted while evaluating a place expression. -/
inductive PlaceReadsName : PlaceExpr → Ident → Prop where
  | var
      {x : Ident} :
      PlaceReadsName (.var x) x

  | deref
      {e : ValExpr} {x : Ident} :
      ValReadsName e x →
      PlaceReadsName (.deref e) x

/-- Names consulted while evaluating a value expression. -/
inductive ValReadsName : ValExpr → Ident → Prop where
  | load
      {p : PlaceExpr} {x : Ident} :
      PlaceReadsName p x →
      ValReadsName (.load p) x

  | addrOf
      {p : PlaceExpr} {x : Ident} :
      PlaceReadsName p x →
      ValReadsName (.addrOf p) x

  | addLeft
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₁ x →
      ValReadsName (.add e₁ e₂) x

  | addRight
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₂ x →
      ValReadsName (.add e₁ e₂) x

  | subLeft
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₁ x →
      ValReadsName (.sub e₁ e₂) x

  | subRight
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₂ x →
      ValReadsName (.sub e₁ e₂) x

  | mulLeft
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₁ x →
      ValReadsName (.mul e₁ e₂) x

  | mulRight
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₂ x →
      ValReadsName (.mul e₁ e₂) x

  | eqLeft
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₁ x →
      ValReadsName (.eq e₁ e₂) x

  | eqRight
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₂ x →
      ValReadsName (.eq e₁ e₂) x

  | ltLeft
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₁ x →
      ValReadsName (.lt e₁ e₂) x

  | ltRight
      {e₁ e₂ : ValExpr} {x : Ident} :
      ValReadsName e₂ x →
      ValReadsName (.lt e₁ e₂) x

  | not
      {e : ValExpr} {x : Ident} :
      ValReadsName e x →
      ValReadsName (.not e) x

end

mutual

/-- A place expression may require a pointer dereference. -/
inductive PlaceDerefUse : PlaceExpr → Prop where
  | derefHere
      {e : ValExpr} :
      PlaceDerefUse (.deref e)

  | derefExpr
      {e : ValExpr} :
      ValDerefUse e →
      PlaceDerefUse (.deref e)

/-- A value expression may require a pointer dereference. -/
inductive ValDerefUse : ValExpr → Prop where
  | loadPlace
      {p : PlaceExpr} :
      PlaceDerefUse p →
      ValDerefUse (.load p)

  | addrOfPlace
      {p : PlaceExpr} :
      PlaceDerefUse p →
      ValDerefUse (.addrOf p)

  | addLeft
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₁ →
      ValDerefUse (.add e₁ e₂)

  | addRight
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₂ →
      ValDerefUse (.add e₁ e₂)

  | subLeft
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₁ →
      ValDerefUse (.sub e₁ e₂)

  | subRight
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₂ →
      ValDerefUse (.sub e₁ e₂)

  | mulLeft
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₁ →
      ValDerefUse (.mul e₁ e₂)

  | mulRight
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₂ →
      ValDerefUse (.mul e₁ e₂)

  | eqLeft
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₁ →
      ValDerefUse (.eq e₁ e₂)

  | eqRight
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₂ →
      ValDerefUse (.eq e₁ e₂)

  | ltLeft
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₁ →
      ValDerefUse (.lt e₁ e₂)

  | ltRight
      {e₁ e₂ : ValExpr} :
      ValDerefUse e₂ →
      ValDerefUse (.lt e₁ e₂)

  | not
      {e : ValExpr} :
      ValDerefUse e →
      ValDerefUse (.not e)

end

/-- Direct source-level name of a place, when the place is syntactically a name. -/
inductive PlaceDirectName : PlaceExpr → Ident → Prop where
  | var
      {x : Ident} :
      PlaceDirectName (.var x) x

/-- Names read while evaluating a condition. -/
inductive CondReadsName : CppCond → Ident → Prop where
  | expr
      {e : ValExpr} {x : Ident} :
      ValReadsName e x →
      CondReadsName (.expr e) x

/-- Conditions that may require a dereference. -/
inductive CondDerefUse : CppCond → Prop where
  | expr
      {e : ValExpr} :
      ValDerefUse e →
      CondDerefUse (.expr e)

/-- Names read while evaluating an initializer. -/
inductive InitReadsName : CppInit → Ident → Prop where
  | value
      {e : ValExpr} {x : Ident} :
      ValReadsName e x →
      InitReadsName (.value e) x

/-- Initializers that may require a dereference. -/
inductive InitDerefUse : CppInit → Prop where
  | value
      {e : ValExpr} :
      ValDerefUse e →
      InitDerefUse (.value e)

/-- Names read by a declaration payload. -/
inductive DeclReadsName : CppDecl → Ident → Prop where
  | objectInit
      {τ : CppType} {x : Ident} {init : CppInit} {y : Ident} :
      InitReadsName init y →
      DeclReadsName (.object τ x init) y

  | refTarget
      {τ : CppType} {x : Ident} {p : PlaceExpr} {y : Ident} :
      PlaceReadsName p y →
      DeclReadsName (.ref τ x p) y

/-- Names introduced by a declaration. -/
inductive DeclBindsName : CppDecl → Ident → Prop where
  | object
      {τ : CppType} {x : Ident} {init : CppInit} :
      DeclBindsName (.object τ x init) x

  | ref
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      DeclBindsName (.ref τ x p) x

/-- Names read by an assignment. -/
inductive AssignReadsName : CppAssign → Ident → Prop where
  | place
      {p : PlaceExpr} {e : ValExpr} {x : Ident} :
      PlaceReadsName p x →
      AssignReadsName (.simple p e) x

  | value
      {p : PlaceExpr} {e : ValExpr} {x : Ident} :
      ValReadsName e x →
      AssignReadsName (.simple p e) x

/-- Direct source-level names written by an assignment.  Pointer writes through
`*p` are intentionally not classified as direct name writes; their safety is a
later dereference/write-boundary matter. -/
inductive AssignWritesDirectName : CppAssign → Ident → Prop where
  | simple
      {p : PlaceExpr} {e : ValExpr} {x : Ident} :
      PlaceDirectName p x →
      AssignWritesDirectName (.simple p e) x

/-- Names read by an expression statement. -/
inductive ExprStmtReadsName : CppExprStmt → Ident → Prop where
  | discard
      {e : ValExpr} {x : Ident} :
      ValReadsName e x →
      ExprStmtReadsName (.discard e) x

/-- Names read by a return payload. -/
inductive ReturnReadsName : CppReturn → Ident → Prop where
  | value
      {e : ValExpr} {x : Ident} :
      ValReadsName e x →
      ReturnReadsName (.value e) x

/-- Names read by a jump. -/
inductive JumpReadsName : CppJump → Ident → Prop where
  | returnStmt
      {r : CppReturn} {x : Ident} :
      ReturnReadsName r x →
      JumpReadsName (.returnStmt r) x

mutual

/-- Names read by a statement. -/
inductive StmtReadsName : CppStmt → Ident → Prop where
  | exprStmt
      {e : CppExprStmt} {x : Ident} :
      ExprStmtReadsName e x →
      StmtReadsName (.exprStmt e) x

  | assign
      {a : CppAssign} {x : Ident} :
      AssignReadsName a x →
      StmtReadsName (.assign a) x

  | decl
      {d : CppDecl} {x : Ident} :
      DeclReadsName d x →
      StmtReadsName (.decl d) x

  | seqLeft
      {s t : CppStmt} {x : Ident} :
      StmtReadsName s x →
      StmtReadsName (.seq s t) x

  | seqRight
      {s t : CppStmt} {x : Ident} :
      StmtReadsName t x →
      StmtReadsName (.seq s t) x

  | iteCond
      {cond : CppCond} {s t : CppStmt} {x : Ident} :
      CondReadsName cond x →
      StmtReadsName (.ite cond s t) x

  | iteThen
      {cond : CppCond} {s t : CppStmt} {x : Ident} :
      StmtReadsName s x →
      StmtReadsName (.ite cond s t) x

  | iteElse
      {cond : CppCond} {s t : CppStmt} {x : Ident} :
      StmtReadsName t x →
      StmtReadsName (.ite cond s t) x

  | whileCond
      {cond : CppCond} {body : CppStmt} {x : Ident} :
      CondReadsName cond x →
      StmtReadsName (.whileStmt cond body) x

  | whileBody
      {cond : CppCond} {body : CppStmt} {x : Ident} :
      StmtReadsName body x →
      StmtReadsName (.whileStmt cond body) x

  | block
      {ss : StmtBlock} {x : Ident} :
      BlockReadsName ss x →
      StmtReadsName (.block ss) x

  | jump
      {j : CppJump} {x : Ident} :
      JumpReadsName j x →
      StmtReadsName (.jump j) x

/-- Names read by a block body. -/
inductive BlockReadsName : StmtBlock → Ident → Prop where
  | consHead
      {head : CppStmt} {tail : StmtBlock} {x : Ident} :
      StmtReadsName head x →
      BlockReadsName (.cons head tail) x

  | consTail
      {head : CppStmt} {tail : StmtBlock} {x : Ident} :
      BlockReadsName tail x →
      BlockReadsName (.cons head tail) x

end

mutual

/-- Direct source-level names written by a statement. -/
inductive StmtWritesDirectName : CppStmt → Ident → Prop where
  | assign
      {a : CppAssign} {x : Ident} :
      AssignWritesDirectName a x →
      StmtWritesDirectName (.assign a) x

  | seqLeft
      {s t : CppStmt} {x : Ident} :
      StmtWritesDirectName s x →
      StmtWritesDirectName (.seq s t) x

  | seqRight
      {s t : CppStmt} {x : Ident} :
      StmtWritesDirectName t x →
      StmtWritesDirectName (.seq s t) x

  | iteThen
      {cond : CppCond} {s t : CppStmt} {x : Ident} :
      StmtWritesDirectName s x →
      StmtWritesDirectName (.ite cond s t) x

  | iteElse
      {cond : CppCond} {s t : CppStmt} {x : Ident} :
      StmtWritesDirectName t x →
      StmtWritesDirectName (.ite cond s t) x

  | whileBody
      {cond : CppCond} {body : CppStmt} {x : Ident} :
      StmtWritesDirectName body x →
      StmtWritesDirectName (.whileStmt cond body) x

  | block
      {ss : StmtBlock} {x : Ident} :
      BlockWritesDirectName ss x →
      StmtWritesDirectName (.block ss) x

/-- Direct source-level names written by a block body. -/
inductive BlockWritesDirectName : StmtBlock → Ident → Prop where
  | consHead
      {head : CppStmt} {tail : StmtBlock} {x : Ident} :
      StmtWritesDirectName head x →
      BlockWritesDirectName (.cons head tail) x

  | consTail
      {head : CppStmt} {tail : StmtBlock} {x : Ident} :
      BlockWritesDirectName tail x →
      BlockWritesDirectName (.cons head tail) x

end

mutual

/-- Names bound by declarations inside a statement. -/
inductive StmtBindsName : CppStmt → Ident → Prop where
  | decl
      {d : CppDecl} {x : Ident} :
      DeclBindsName d x →
      StmtBindsName (.decl d) x

  | seqLeft
      {s t : CppStmt} {x : Ident} :
      StmtBindsName s x →
      StmtBindsName (.seq s t) x

  | seqRight
      {s t : CppStmt} {x : Ident} :
      StmtBindsName t x →
      StmtBindsName (.seq s t) x

  | iteThen
      {cond : CppCond} {s t : CppStmt} {x : Ident} :
      StmtBindsName s x →
      StmtBindsName (.ite cond s t) x

  | iteElse
      {cond : CppCond} {s t : CppStmt} {x : Ident} :
      StmtBindsName t x →
      StmtBindsName (.ite cond s t) x

  | whileBody
      {cond : CppCond} {body : CppStmt} {x : Ident} :
      StmtBindsName body x →
      StmtBindsName (.whileStmt cond body) x

  | block
      {ss : StmtBlock} {x : Ident} :
      BlockBindsName ss x →
      StmtBindsName (.block ss) x

/-- Names bound by declarations inside a block body. -/
inductive BlockBindsName : StmtBlock → Ident → Prop where
  | consHead
      {head : CppStmt} {tail : StmtBlock} {x : Ident} :
      StmtBindsName head x →
      BlockBindsName (.cons head tail) x

  | consTail
      {head : CppStmt} {tail : StmtBlock} {x : Ident} :
      BlockBindsName tail x →
      BlockBindsName (.cons head tail) x

end

end Effects
end Cpp3
