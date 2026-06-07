import CppFormalization.Cpp3.Static.WellFormed

/-!
# CppFormalization.Cpp3.Static.Scope

Static scope surfaces that are independent of runtime readiness.

The purpose of this file is not to rebuild `Typing.Judgment`.  It only names the
scope-facing static facts that later Boundary/Effects/Stability layers can reuse:
current-scope freshness, declaration environment effects, and opened block scope
surfaces.
-/

namespace Cpp3
namespace Static

/-- A declaration name is fresh in the current static scope. -/
abbrev StaticNameFresh (Γ : TypeEnv) (x : Ident) : Prop :=
  currentTypeScopeFresh Γ x

/-- Static environment effect of a declaration. -/
inductive StaticDeclEnvEffect : TypeEnv → CppDecl → TypeEnv → Prop where
  | object
      {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {init : CppInit} :
      StaticObjectType τ →
      StaticInitFormed init →
      StaticNameFresh Γ x →
      Δ = declareTypeObject Γ x τ →
      StaticDeclEnvEffect Γ (.object τ x init) Δ

  | ref
      {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr} :
      StaticReferenceTargetType τ →
      StaticPlaceFormed p →
      StaticNameFresh Γ x →
      Δ = declareTypeRef Γ x τ →
      StaticDeclEnvEffect Γ (.ref τ x p) Δ

/-- Static scope entry for a block body. -/
structure StaticBlockScopeEntry (Γ Γopen : TypeEnv) : Type where
  opened : Γopen = pushTypeScope Γ

/-- Static public block-exit surface.

A C++ block statement exposes the outer type environment again.  The opened body
may compute through `Γopen` and `Θ`, but this thin static layer records only the
public `Γ → Γ` surface. -/
structure StaticBlockScopeExit (Γ Γopen Θ Δ : TypeEnv) : Type where
  exitsOuter : Δ = Γ

namespace StaticBlockScopeEntry

/-- The canonical opened static environment for a block entered from `Γ`. -/
def canonical (Γ : TypeEnv) : StaticBlockScopeEntry Γ (pushTypeScope Γ) where
  opened := rfl

end StaticBlockScopeEntry

namespace StaticBlockScopeExit

/-- The canonical public exit for a block statement. -/
def canonical (Γ Γopen Θ : TypeEnv) : StaticBlockScopeExit Γ Γopen Θ Γ where
  exitsOuter := rfl

end StaticBlockScopeExit

end Static
end Cpp3
