import CppFormalization.Cpp2.Proof.Preservation.Demand.CompositePreservation
import CppFormalization.Cpp2.Proof.Preservation.Scope.OpenPreservation
import CppFormalization.Cpp2.Proof.Preservation.Scope.ClosePreservation

namespace Cpp

/-!
# Proof.Preservation.Demand.FullPreservation

Theorem-backed preservation components for the path-sensitive demand route.

This file advances the demand route to the point just before removing the old
` 削除済み` route.  The key addition is block statement
preservation: demand now carries the `TopFrameExtensionOf Γ Θ` witness needed
to close the runtime scope and return to the outer environment.
-/

/--
Preservation for a block statement from path-sensitive demand.

This theorem is the demand-side analogue of the old block-statement preservation
route, but it does not need `BlockReadyConcrete` transport.  The opened block
body demand is already stated at the opened runtime scope, and the demanded body
post-environment carries the top-frame-extension witness required by
`CloseScope`.
-/
theorem block_stmt_preserves_from_demand
    {Γ : TypeEnv} {σ σ₂ : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (hdemand : StmtExecutionDemand Γ σ (.block ss) ctrl σ₂ Γ)
    (hbody :
      ∀ {Θ : TypeEnv} {σ₀ σ₁ : State},
        TopFrameExtensionOf Γ Θ →
        BlockExecutionDemand (pushTypeScope Γ) σ₀ ss ctrl σ₁ Θ →
        ScopedTypedStateConcrete (pushTypeScope Γ) σ₀ →
        ScopedTypedStateConcrete Θ σ₁) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ₂ := by
  intro hσ
  cases hdemand with
  | block hopen hExt hbodyDemand hclose =>
      have hσ₀ : ScopedTypedStateConcrete (pushTypeScope Γ) _ :=
        openScope_preserves_scoped_typed_state_concrete hσ hopen
      have hσ₁ : ScopedTypedStateConcrete _ _ :=
        hbody hExt hbodyDemand hσ₀
      exact closeScope_preserves_outer_from_topFrameExtension hExt hσ₁ hclose

/--
A public alias emphasizing that this theorem is the block-scope component of the
future full demand recursor.
-/
theorem block_scope_component_from_demand
    {Γ : TypeEnv} {σ σ₂ : State} {ss : StmtBlock} {ctrl : CtrlResult} :
    StmtExecutionDemand Γ σ (.block ss) ctrl σ₂ Γ →
    (∀ {Θ : TypeEnv} {σ₀ σ₁ : State},
        TopFrameExtensionOf Γ Θ →
        BlockExecutionDemand (pushTypeScope Γ) σ₀ ss ctrl σ₁ Θ →
        ScopedTypedStateConcrete (pushTypeScope Γ) σ₀ →
        ScopedTypedStateConcrete Θ σ₁) →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ₂ :=
  block_stmt_preserves_from_demand

end Cpp
