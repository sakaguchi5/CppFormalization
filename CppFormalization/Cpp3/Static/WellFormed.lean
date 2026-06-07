import CppFormalization.Cpp3.Core.All

/-!
# CppFormalization.Cpp3.Static.WellFormed

Syntax-only static formation for the Cpp3 core fragment.

This layer intentionally does not import Typing, Semantics, Boundary,
Stability, or Soundness.  It records which syntax belongs to the current
statically admitted C++ fragment before any runtime state is considered.
-/

namespace Cpp3
namespace Static

/-- Object types admitted by the current static fragment. -/
abbrev StaticObjectType (τ : CppType) : Prop :=
  ObjectType τ

/-- Reference target types admitted by the current static fragment.

For now references target the same object-type fragment as object declarations:
no `void`, no reference-to-reference payloads, and no arrays in the executable
core fragment. -/
abbrev StaticReferenceTargetType (τ : CppType) : Prop :=
  ObjectType τ

mutual

/-- Static formation for place expressions. -/
inductive StaticPlaceFormed : PlaceExpr → Prop where
  | var
      {x : Ident} :
      StaticPlaceFormed (.var x)

  | deref
      {e : ValExpr} :
      StaticValFormed e →
      StaticPlaceFormed (.deref e)

/-- Static formation for value expressions. -/
inductive StaticValFormed : ValExpr → Prop where
  | litBool
      {b : Bool} :
      StaticValFormed (.litBool b)

  | litInt
      {n : Int} :
      StaticValFormed (.litInt n)

  | load
      {p : PlaceExpr} :
      StaticPlaceFormed p →
      StaticValFormed (.load p)

  | addrOf
      {p : PlaceExpr} :
      StaticPlaceFormed p →
      StaticValFormed (.addrOf p)

  | add
      {e₁ e₂ : ValExpr} :
      StaticValFormed e₁ →
      StaticValFormed e₂ →
      StaticValFormed (.add e₁ e₂)

  | sub
      {e₁ e₂ : ValExpr} :
      StaticValFormed e₁ →
      StaticValFormed e₂ →
      StaticValFormed (.sub e₁ e₂)

  | mul
      {e₁ e₂ : ValExpr} :
      StaticValFormed e₁ →
      StaticValFormed e₂ →
      StaticValFormed (.mul e₁ e₂)

  | eq
      {e₁ e₂ : ValExpr} :
      StaticValFormed e₁ →
      StaticValFormed e₂ →
      StaticValFormed (.eq e₁ e₂)

  | lt
      {e₁ e₂ : ValExpr} :
      StaticValFormed e₁ →
      StaticValFormed e₂ →
      StaticValFormed (.lt e₁ e₂)

  | not
      {e : ValExpr} :
      StaticValFormed e →
      StaticValFormed (.not e)

end

/-- Static formation for control conditions. -/
inductive StaticCondFormed : CppCond → Prop where
  | expr
      {e : ValExpr} :
      StaticValFormed e →
      StaticCondFormed (.expr e)

/-- Static formation for declaration initializers. -/
inductive StaticInitFormed : CppInit → Prop where
  | noInit :
      StaticInitFormed .noInit

  | value
      {e : ValExpr} :
      StaticValFormed e →
      StaticInitFormed (.value e)

/-- Static formation for declarations, independent of name freshness. -/
inductive StaticDeclFormed : CppDecl → Prop where
  | object
      {τ : CppType} {x : Ident} {init : CppInit} :
      StaticObjectType τ →
      StaticInitFormed init →
      StaticDeclFormed (.object τ x init)

  | ref
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      StaticReferenceTargetType τ →
      StaticPlaceFormed p →
      StaticDeclFormed (.ref τ x p)

/-- Static formation for return payloads. -/
inductive StaticReturnFormed : CppReturn → Prop where
  | void :
      StaticReturnFormed .void

  | value
      {e : ValExpr} :
      StaticValFormed e →
      StaticReturnFormed (.value e)

/-- Static formation for jumps. -/
inductive StaticJumpFormed : CppJump → Prop where
  | breakStmt :
      StaticJumpFormed .breakStmt

  | continueStmt :
      StaticJumpFormed .continueStmt

  | returnStmt
      {r : CppReturn} :
      StaticReturnFormed r →
      StaticJumpFormed (.returnStmt r)

/-- Static formation for assignments. -/
inductive StaticAssignFormed : CppAssign → Prop where
  | simple
      {p : PlaceExpr} {e : ValExpr} :
      StaticPlaceFormed p →
      StaticValFormed e →
      StaticAssignFormed (.simple p e)

/-- Static formation for expression statements. -/
inductive StaticExprStmtFormed : CppExprStmt → Prop where
  | discard
      {e : ValExpr} :
      StaticValFormed e →
      StaticExprStmtFormed (.discard e)

mutual

/-- Static formation for statements. -/
inductive StaticStmtFormed : CppStmt → Prop where
  | skip :
      StaticStmtFormed .skip

  | exprStmt
      {e : CppExprStmt} :
      StaticExprStmtFormed e →
      StaticStmtFormed (.exprStmt e)

  | assign
      {a : CppAssign} :
      StaticAssignFormed a →
      StaticStmtFormed (.assign a)

  | decl
      {d : CppDecl} :
      StaticDeclFormed d →
      StaticStmtFormed (.decl d)

  | seq
      {s t : CppStmt} :
      StaticStmtFormed s →
      StaticStmtFormed t →
      StaticStmtFormed (.seq s t)

  | ite
      {cond : CppCond} {s t : CppStmt} :
      StaticCondFormed cond →
      StaticStmtFormed s →
      StaticStmtFormed t →
      StaticStmtFormed (.ite cond s t)

  | whileStmt
      {cond : CppCond} {body : CppStmt} :
      StaticCondFormed cond →
      StaticStmtFormed body →
      StaticStmtFormed (.whileStmt cond body)

  | block
      {ss : StmtBlock} :
      StaticBlockFormed ss →
      StaticStmtFormed (.block ss)

  | jump
      {j : CppJump} :
      StaticJumpFormed j →
      StaticStmtFormed (.jump j)

/-- Static formation for statement blocks. -/
inductive StaticBlockFormed : StmtBlock → Prop where
  | nil :
      StaticBlockFormed .nil

  | cons
      {s : CppStmt} {ss : StmtBlock} :
      StaticStmtFormed s →
      StaticBlockFormed ss →
      StaticBlockFormed (.cons s ss)

end

end Static
end Cpp3
