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

/-- Primitive control effect of a primitive statement. -/
inductive PrimitiveControlEffect : CppStmt → ControlKind → Prop where
  | skip :
      PrimitiveControlEffect .skip .normalK

  | exprStmt
      {e : ValExpr} :
      PrimitiveControlEffect (.exprStmt e) .normalK

  | assign
      {p : PlaceExpr} {e : ValExpr} :
      PrimitiveControlEffect (.assign p e) .normalK

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
