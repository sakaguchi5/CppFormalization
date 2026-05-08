import CppFormalization.Cpp2.Closure.Internal.SeqNormalPreservationProviderCI

namespace Cpp

/-!
# Closure.Internal.SeqNormalPreservationCoreCI

Pure normal-preservation core extracted from the current provider-shaped seq
surface.

`StmtNormalPreservationProviderCI` currently still carries a compatibility field
for older theorem surfaces that bottom out in `WhileReentryReadyProvider`.
That field is an implementation bridge, not the mathematical dependency of
`seq`.

This file names the genuinely seq-facing dependency:

* if the left statement of a sequence finishes normally, the post-state remains
  scoped/typed at the left post-environment.

The lower residual-boundary reconstruction for `seq` is then proved from this
pure core, with no mention of while reentry.
-/

/--
Pure provider for generic statement normal preservation.

This is the dependency that sequencing actually needs.  It says nothing about
while reentry or next-loop readiness.
-/
structure StmtNormalPreservationCoreCI : Type where
  preserve :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt},
      HasTypeStmtCI .normalK Γ st Δ →
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ st →
      BigStepStmt σ st .normal σ' →
      ScopedTypedStateConcrete Δ σ'

namespace StmtNormalPreservationCoreCI

/-- Use the pure provider as a left-preservation callback for a fixed left side. -/
def leftPreservation
    (P : StmtNormalPreservationCoreCI)
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} :
    ∀ {Θ : TypeEnv},
      HasTypeStmtCI .normalK Γ s Θ →
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Θ σ' := by
  intro Θ htyLeft hσ hreadyLeft hstepLeft
  exact P.preserve htyLeft hσ hreadyLeft hstepLeft

end StmtNormalPreservationCoreCI

namespace StmtNormalPreservationProviderCI

/-- Forget the current compatibility provider to the pure seq-facing core. -/
def toCore (P : StmtNormalPreservationProviderCI) :
    StmtNormalPreservationCoreCI :=
  { preserve := P.preserve }

end StmtNormalPreservationProviderCI

/--
Build the pure normal-preservation core from the current while-reentry provider.

This is a compatibility bridge for existing global preservation.  New seq-facing
statements should target `StmtNormalPreservationCoreCI`; construction of the core
from while reentry is an implementation detail.
-/
def stmtNormalPreservationCoreCI_of_whileReentry
    (mkWhileReentry : WhileReentryReadyProvider) :
    StmtNormalPreservationCoreCI :=
  (stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry).toCore

/--
Sequence residual-boundary reconstruction from the pure normal-preservation core.

This is the theorem that captures the real mathematical dependency of `seq`:
left-normal preservation.  It does not mention while reentry.
-/
theorem seq_left_normal_preserves_residual_boundary_of_normal_preservation_core
    (P : StmtNormalPreservationCoreCI)
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
Fixed-post-environment ready/state reconstruction from the pure
normal-preservation core.
-/
theorem seq_left_normal_preserves_ready_of_normal_preservation_core
    (P : StmtNormalPreservationCoreCI)
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

/--
Compatibility corollary: the previous provider-shaped theorem factors through
the pure core.
-/
theorem seq_left_normal_preserves_residual_boundary_of_provider_core
    (P : StmtNormalPreservationProviderCI)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t :=
  seq_left_normal_preserves_residual_boundary_of_normal_preservation_core P.toCore

/--
Compatibility corollary for the fixed-post-environment ready/state surface.
-/
theorem seq_left_normal_preserves_ready_of_provider_core
    (P : StmtNormalPreservationProviderCI)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t :=
  seq_left_normal_preserves_ready_of_normal_preservation_core P.toCore

end Cpp
