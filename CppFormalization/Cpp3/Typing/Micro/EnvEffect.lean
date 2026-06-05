import CppFormalization.Cpp3.Typing.Micro.ControlEffect

namespace Cpp3
namespace Typing
namespace Micro

/-!
# CppFormalization.Cpp3.Typing.Micro.EnvEffect

Primitive type-environment effects.

This file records only the local static environment transition of primitive
statements.  It does not assert semantic preservation and it does not transport
readiness.
-/

/-- Primitive type-environment effect of a primitive statement. -/
inductive PrimitiveEnvEffect : TypeEnv → CppStmt → TypeEnv → Prop where
  | skip
      {Γ : TypeEnv} :
      PrimitiveEnvEffect Γ .skip Γ

  | exprStmt
      {Γ : TypeEnv} {e : ValExpr} :
      PrimitiveEnvEffect Γ (.exprStmt e) Γ

  | assign
      {Γ : TypeEnv} {p : PlaceExpr} {e : ValExpr} :
      PrimitiveEnvEffect Γ (.assign p e) Γ

  | declareObj
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {oe : Option ValExpr} :
      PrimitiveEnvEffect Γ (.declareObj τ x oe) (declareTypeObject Γ x τ)

  | declareRef
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr} :
      PrimitiveEnvEffect Γ (.declareRef τ x p) (declareTypeRef Γ x τ)

  | breakStmt
      {Γ : TypeEnv} :
      PrimitiveEnvEffect Γ .breakStmt Γ

  | continueStmt
      {Γ : TypeEnv} :
      PrimitiveEnvEffect Γ .continueStmt Γ

  | returnStmt
      {Γ : TypeEnv} {oe : Option ValExpr} :
      PrimitiveEnvEffect Γ (.returnStmt oe) Γ

end Micro
end Typing
end Cpp3
