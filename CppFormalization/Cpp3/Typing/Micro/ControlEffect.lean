import CppFormalization.Cpp3.Typing.Micro.Formation

namespace Cpp3
namespace Typing
namespace Micro

/-!
# CppFormalization.Cpp3.Typing.Micro.ControlEffect

Primitive control-channel effects.

This is still static and local: it records the control kind produced by a
primitive statement shape.  Compound propagation is handled separately.
-/

/-- Non-normal control kinds. -/
inductive AbruptKind : ControlKind → Prop where
  | breakK : AbruptKind .breakK
  | continueK : AbruptKind .continueK
  | returnK : AbruptKind .returnK

/-- Control effect of a jump payload. -/
inductive JumpControlEffect : CppJump → ControlKind → Prop where
  | breakStmt :
      JumpControlEffect .breakStmt .breakK

  | continueStmt :
      JumpControlEffect .continueStmt .continueK

  | returnStmt
      {r : CppReturn} :
      JumpControlEffect (.returnStmt r) .returnK

/-- Control effect of an assignment payload. -/
inductive AssignControlEffect : CppAssign → ControlKind → Prop where
  | simple
      {p : PlaceExpr} {e : ValExpr} :
      AssignControlEffect (.simple p e) .normalK

/-- Control effect of an expression-statement payload. -/
inductive ExprStmtControlEffect : CppExprStmt → ControlKind → Prop where
  | discard
      {e : ValExpr} :
      ExprStmtControlEffect (.discard e) .normalK

/-- Primitive control effect of a primitive statement. -/
inductive PrimitiveControlEffect : CppStmt → ControlKind → Prop where
  | skip :
      PrimitiveControlEffect .skip .normalK

  | exprStmt
      {es : CppExprStmt} {k : ControlKind} :
      ExprStmtControlEffect es k →
      PrimitiveControlEffect (.exprStmt es) k

  | assign
      {a : CppAssign} {k : ControlKind} :
      AssignControlEffect a k →
      PrimitiveControlEffect (.assign a) k

  | decl
      {d : CppDecl} :
      PrimitiveControlEffect (.decl d) .normalK

  | jump
      {j : CppJump} {k : ControlKind} :
      JumpControlEffect j k →
      PrimitiveControlEffect (.jump j) k

end Micro
end Typing
end Cpp3
