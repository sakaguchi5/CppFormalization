import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI

namespace Cpp

/-!
# Closure.Foundation.BodyBoundaryCI

Compatibility wrapper after the static-layer redesign.

This is intentionally no longer a flat record.
The old flat surface was exactly what encouraged incoherent combinations of
`typed0 / entry / summary`.
-/

structure BodyReadyCI (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

structure BlockBodyReadyCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  structural : BlockBodyStructuralBoundary Γ ss
  static : BlockBodyStaticBoundaryCI Γ ss
  dynamic : BlockBodyDynamicBoundary Γ σ ss
  adequacy : BlockBodyAdequacyCI Γ σ ss static.profile

theorem break_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .breakResult σ' := by
  intro σ' hstep
  exact stmt_break_not_scoped hstep h.structural.breakScoped

theorem continue_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .continueResult σ' := by
  intro σ' hstep
  exact stmt_continue_not_scoped hstep h.structural.continueScoped

theorem top_level_abrupt_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyReadyCI Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact stmt_break_not_scoped hbreak hready.structural.breakScoped
  · intro hcont
    exact stmt_continue_not_scoped hcont hready.structural.continueScoped

theorem top_level_abrupt_excluded_from_blockBodyReadyCI
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyReadyCI Γ σ ss →
    ¬ BigStepBlock σ ss .breakResult σ' ∧ ¬ BigStepBlock σ ss .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact no_top_break_from_scoped_block hready.structural.breakScoped hbreak
  · intro hcont
    exact no_top_continue_from_scoped_block hready.structural.continueScoped hcont

end Cpp
