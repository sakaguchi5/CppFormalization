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

/-- Type-environment effect of a declaration. -/
inductive DeclEnvEffect : TypeEnv → CppDecl → TypeEnv → Prop where
  | object
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {init : CppInit} :
      DeclEnvEffect Γ (.object τ x init) (declareTypeObject Γ x τ)

  | ref
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr} :
      DeclEnvEffect Γ (.ref τ x p) (declareTypeRef Γ x τ)

/-- Type-environment effect of a jump.

Break/continue/return do not extend the static environment; they only change the
control channel. -/
inductive JumpEnvEffect : TypeEnv → CppJump → TypeEnv → Prop where
  | jump
      {Γ : TypeEnv} {j : CppJump} :
      JumpEnvEffect Γ j Γ

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

  | decl
      {Γ Δ : TypeEnv} {d : CppDecl} :
      DeclEnvEffect Γ d Δ →
      PrimitiveEnvEffect Γ (.decl d) Δ

  | jump
      {Γ Δ : TypeEnv} {j : CppJump} :
      JumpEnvEffect Γ j Δ →
      PrimitiveEnvEffect Γ (.jump j) Δ

end Micro
end Typing
end Cpp3
