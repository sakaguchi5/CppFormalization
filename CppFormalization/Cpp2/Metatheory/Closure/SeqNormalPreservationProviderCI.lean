import CppFormalization.Cpp2.Preservation.Closure.SequentialNormalPreservation
import CppFormalization.Cpp2.Preservation.Closure.StmtControlPreservation

namespace Cpp

/-!
# Closure.Internal.SeqNormalPreservationProviderCI

Provider surface for statement-normal preservation.

Sequencing needs two facts after the left side finishes normally:

* generic normal preservation for the left statement;
* an explicit post-route tail continuation boundary for the right statement.

The second fact replaces the old `削除済みaxiom` route.
-/

/--
Provider for generic statement normal preservation.

`preserve` is the abstraction needed by `seq` after the left statement finishes
normally.  New seq-facing code should pair this provider with an explicit tail
continuation provider rather than asking this provider to transport readiness.
-/
structure StmtNormalPreservationProviderCI : Type where
  preserve :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt},
      HasTypeStmtCI .normalK Γ st Δ →
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ st →
      BigStepStmt σ st .normal σ' →
      ScopedTypedStateConcrete Δ σ'

namespace StmtNormalPreservationProviderCI

/-- Apply the provider as a left-preservation callback for a fixed left statement. -/
def leftPreservation
    (P : StmtNormalPreservationProviderCI)
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} :
    ∀ {Θ : TypeEnv},
      HasTypeStmtCI .normalK Γ s Θ →
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Θ σ' := by
  intro Θ htyLeft hσ hreadyLeft hstepLeft
  exact P.preserve htyLeft hσ hreadyLeft hstepLeft

end StmtNormalPreservationProviderCI

/--
Build the normal-preservation provider from the current while-reentry provider.

This bridge is intentionally one-way: old code can still supply global statement
normal preservation, but seq-facing code must separately supply post-route tail
continuation evidence.
-/
def stmtNormalPreservationProviderCI_of_whileReentry :
    StmtNormalPreservationProviderCI :=
  { preserve := by
      intro Γ Δ σ σ' st hty hσ hready hstep
      exact
        stmt_normal_preserves_scoped_typed_state_concrete
          hty hσ hready hstep }

/--
Sequence residual-boundary reconstruction from the generic normal-preservation
provider plus explicit tail continuation evidence.
-/
theorem seq_left_normal_preserves_residual_boundary_of_normal_preservation_provider
    (P : StmtNormalPreservationProviderCI)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (htail :
      ∀ {Θ : TypeEnv},
        HasTypeStmtCI .normalK Γ s Θ →
        HasTypeStmtCI .normalK Θ t Δ →
        ScopedTypedStateConcrete Θ σ' →
        StmtReadyConcrete Γ σ (.seq s t) →
        BigStepStmt σ s .normal σ' →
        StmtContinuationDynamicBoundary Θ σ' t) :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro htySeq hσ hreadySeq hstepLeft
  exact
    seq_left_normal_preserves_residual_boundary_of_left_preservation
      (s := s) (t := t) (Γ := Γ) (Δ := Δ) (σ := σ) (σ' := σ')
      (hpres := P.leftPreservation)
      (htail := htail)
      htySeq hσ hreadySeq hstepLeft

/--
Fixed-post-environment ready/state reconstruction from the generic
normal-preservation provider plus explicit tail continuation evidence.
-/
theorem seq_left_normal_preserves_ready_of_normal_preservation_provider
    (P : StmtNormalPreservationProviderCI)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (htail :
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Δ σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtContinuationDynamicBoundary Δ σ' t) :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t := by
  intro htyLeft hreadySeq hstepLeft hσ
  exact
    seq_left_normal_preserves_ready_of_left_preservation
      (s := s) (t := t) (Γ := Γ) (Δ := Δ) (σ := σ) (σ' := σ')
      (hpres := by
        intro htyLeft' hσ0 hreadyLeft hstepLeft0
        exact P.preserve htyLeft' hσ0 hreadyLeft hstepLeft0)
      (htail := htail)
      htyLeft hreadySeq hstepLeft hσ

/-- Compatibility corollary for older callers, with tail continuation explicit. -/
theorem seq_left_normal_preserves_residual_boundary_of_whileReentry
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (htail :
      ∀ {Θ : TypeEnv},
        HasTypeStmtCI .normalK Γ s Θ →
        HasTypeStmtCI .normalK Θ t Δ →
        ScopedTypedStateConcrete Θ σ' →
        StmtReadyConcrete Γ σ (.seq s t) →
        BigStepStmt σ s .normal σ' →
        StmtContinuationDynamicBoundary Θ σ' t) :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t :=
  seq_left_normal_preserves_residual_boundary_of_normal_preservation_provider
    (stmtNormalPreservationProviderCI_of_whileReentry) htail

/-- Compatibility corollary for the fixed-post-environment ready/state surface. -/
theorem seq_left_normal_preserves_ready_of_whileReentry
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (htail :
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Δ σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtContinuationDynamicBoundary Δ σ' t) :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t :=
  seq_left_normal_preserves_ready_of_normal_preservation_provider
    (stmtNormalPreservationProviderCI_of_whileReentry) htail

end Cpp
