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

  | declareObj
      {τ : CppType} {x : Ident} {oe : Option ValExpr} :
      PrimitiveControlEffect (.declareObj τ x oe) .normalK

  | declareRef
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      PrimitiveControlEffect (.declareRef τ x p) .normalK

  | breakStmt :
      PrimitiveControlEffect .breakStmt .breakK

  | continueStmt :
      PrimitiveControlEffect .continueStmt .continueK

  | returnStmt
      {oe : Option ValExpr} :
      PrimitiveControlEffect (.returnStmt oe) .returnK

end Micro
end Typing
end Cpp3
