import CppFormalization.Cpp2.Preservation.Closure.SequentialNormalPreservation
import CppFormalization.Cpp2.Preservation.Closure.StmtControlPreservation

namespace Cpp

/-!
# Closure.Internal.SeqNormalPreservationProviderCI

Provider surface for statement-normal preservation.

The point of this layer is to keep `seq` from depending on
`WhileReentryReadyProvider` as vocabulary.  Sequencing only needs the generic
normal-preservation fact for its left statement.  The current implementation of
that generic preservation fact is still built from while reentry, so this file
keeps a compatibility bridge.  The public seq-facing theorems should mention the
normal-preservation provider, not the while reentry provider directly.
-/

/--
Provider for generic statement normal preservation.

`preserve` is the abstraction needed by `seq` after the left statement finishes
normally.  The `reentry` field is retained as implementation evidence for the
current global preservation theorem and for compatibility wrappers that still
bottom out in older while-reentry surfaces.  New seq-facing code should use
`preserve` conceptually.
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

This bridge is intentionally one-way: old code can still supply
`WhileReentryReadyProvider`, but seq-facing code can talk only about generic
normal preservation.
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
provider.
-/
theorem seq_left_normal_preserves_residual_boundary_of_normal_preservation_provider
    (P : StmtNormalPreservationProviderCI)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
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
      htySeq hσ hreadySeq hstepLeft

/--
Fixed-post-environment ready/state reconstruction from the generic
normal-preservation provider.
-/
theorem seq_left_normal_preserves_ready_of_normal_preservation_provider
    (P : StmtNormalPreservationProviderCI)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
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
      htyLeft hreadySeq hstepLeft hσ

/-- Compatibility corollary for older callers. -/
theorem seq_left_normal_preserves_residual_boundary_of_whileReentry
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t :=
  seq_left_normal_preserves_residual_boundary_of_normal_preservation_provider
    (stmtNormalPreservationProviderCI_of_whileReentry)

/-- Compatibility corollary for the fixed-post-environment ready/state surface. -/
theorem seq_left_normal_preserves_ready_of_whileReentry
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t :=
  seq_left_normal_preserves_ready_of_normal_preservation_provider
    (stmtNormalPreservationProviderCI_of_whileReentry )

end Cpp
