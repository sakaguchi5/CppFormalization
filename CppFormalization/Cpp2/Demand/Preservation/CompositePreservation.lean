import CppFormalization.Cpp2.Demand.Preservation.PrimitivePreservation
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete

namespace Cpp

/-!
# Proof.Preservation.Demand.CompositePreservation

Axiom-free composite preservation combinators for path-sensitive demand.

These theorems are the direct replacement shape for the old
` 削除済み` use in `seq` and block `cons`.

Instead of proving that readiness is transported from the pre-state to the
post-state, we consume the post-state tail demand already stored in
`StmtExecutionDemand.seqNormal` / `BlockExecutionDemand.consNormal`.
-/

/--
Demand-preservation combinator for `s; t`.

In the normal-head case, the head demand gives the post-state invariant and the
tail demand is already stated at that post-state.  In abrupt-head cases, the tail
is not executed and the head preservation result is the whole result.
-/
theorem seq_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ₂ : State} {s t : CppStmt} {ctrl : CtrlResult}
    (hdemand : StmtExecutionDemand Γ σ (.seq s t) ctrl σ₂ Δ)
    (hheadNormal :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        StmtExecutionDemand Γ σ s .normal σ₁ Θ →
        ScopedTypedStateConcrete Γ σ →
        ScopedTypedStateConcrete Θ σ₁)
    (htail :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ →
        ScopedTypedStateConcrete Θ σ₁ →
        ScopedTypedStateConcrete Δ σ₂)
    (hheadAbrupt :
      StmtExecutionDemand Γ σ s ctrl σ₂ Δ →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ₂) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ₂ := by
  intro hσ
  cases hdemand with
  | seqNormal hHead hTail =>
      exact htail hTail (hheadNormal hHead hσ)
  | seqBreak hHead =>
      exact hheadAbrupt hHead hσ
  | seqContinue hHead =>
      exact hheadAbrupt hHead hσ
  | seqReturn hHead =>
      exact hheadAbrupt hHead hσ

/-
The old reading was a readiness-transport component.

In the successor vocabulary, this is the block-cons normal successor:
after the head statement exits normally, the tail boundary is reconstructed
under the post-head environment and state.
-/
theorem cons_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ₂ : State} {s : CppStmt} {ss : StmtBlock}
    {ctrl : CtrlResult}
    (hdemand : BlockExecutionDemand Γ σ (.cons s ss) ctrl σ₂ Δ)
    (hheadNormal :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        StmtExecutionDemand Γ σ s .normal σ₁ Θ →
        ScopedTypedStateConcrete Γ σ →
        ScopedTypedStateConcrete Θ σ₁)
    (htail :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ →
        ScopedTypedStateConcrete Θ σ₁ →
        ScopedTypedStateConcrete Δ σ₂)
    (hheadAbrupt :
      StmtExecutionDemand Γ σ s ctrl σ₂ Δ →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ₂) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ₂ := by
  intro hσ
  cases hdemand with
  | consNormal hHead hTail =>
      exact htail hTail (hheadNormal hHead hσ)
  | consBreak hHead =>
      exact hheadAbrupt hHead hσ
  | consContinue hHead =>
      exact hheadAbrupt hHead hσ
  | consReturn hHead =>
      exact hheadAbrupt hHead hσ

/--
Demand-preservation combinator for `if`.

Only the branch selected by the concrete condition execution is consumed.  This
matches C++ execution: the unselected branch need not have runtime demand at the
current state.
-/
theorem ite_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt}
    {ctrl : CtrlResult}
    (hdemand : StmtExecutionDemand Γ σ (.ite c s t) ctrl σ' Δ)
    (hthen :
      StmtExecutionDemand Γ σ s ctrl σ' Δ →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ')
    (helse :
      StmtExecutionDemand Γ σ t ctrl σ' Δ →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ') :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ
  cases hdemand with
  | iteTrue _hc _hready _hcond hbranch =>
      exact hthen hbranch hσ
  | iteFalse _hc _hready _hcond hbranch =>
      exact helse hbranch hσ

/--
Demand-preservation combinator for `while`.

This is intentionally phrased in terms of recursive sub-preservation arguments.
It does not assume that condition/body readiness is transported between
iterations.  If another iteration is executed, the tail demand is already stored
at the re-entry state.
-/
theorem while_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {ctrl : CtrlResult}
    (hdemand : StmtExecutionDemand Γ σ (.whileStmt c body) ctrl σ' Δ)
    (hbodyNormal :
      ∀ {σ₁ : State},
        StmtExecutionDemand Γ σ body .normal σ₁ Γ →
        ScopedTypedStateConcrete Γ σ →
        ScopedTypedStateConcrete Γ σ₁)
    (hbodyBreak :
      ∀ {σ₁ : State},
        StmtExecutionDemand Γ σ body .breakResult σ₁ Γ →
        ScopedTypedStateConcrete Γ σ →
        ScopedTypedStateConcrete Γ σ₁)
    (hbodyContinue :
      ∀ {σ₁ : State},
        StmtExecutionDemand Γ σ body .continueResult σ₁ Γ →
        ScopedTypedStateConcrete Γ σ →
        ScopedTypedStateConcrete Γ σ₁)
    (hbodyReturn :
      ∀ {Δ' : TypeEnv} {σ₁ : State} {rv : Option Value},
        StmtExecutionDemand Γ σ body (.returnResult rv) σ₁ Δ' →
        ScopedTypedStateConcrete Γ σ →
        ScopedTypedStateConcrete Δ' σ₁)
    (htail :
      ∀ {σ₁ : State},
        StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ' Δ →
        ScopedTypedStateConcrete Γ σ₁ →
        ScopedTypedStateConcrete Δ σ') :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ
  cases hdemand with
  | whileFalse _hc _hready _hcond =>
      simpa using hσ
  | whileTrueNormal _hc _hready _hcond hBody hTail =>
      exact htail hTail (hbodyNormal hBody hσ)
  | whileTrueBreak _hc _hready _hcond hBody =>
      exact hbodyBreak hBody hσ
  | whileTrueContinue _hc _hready _hcond hBody hTail =>
      exact htail hTail (hbodyContinue hBody hσ)
  | whileTrueReturn _hc _hready _hcond hBody =>
      exact hbodyReturn hBody hσ

end Cpp
