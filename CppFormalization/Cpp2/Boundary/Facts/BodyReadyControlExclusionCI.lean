import CppFormalization.Cpp2.Boundary.Body.BodyReadyCI
import CppFormalization.Cpp2.Static.Safety.Facts.ControlExclusion

namespace Cpp

/-!
# BodyReadyCI control-exclusion facts

Semantic consequences of a full ready boundary and structural scopedness.

The ready object itself lives in `Boundary.Body.BodyReadyCI`; these facts are
separated because they connect that boundary to big-step execution.
-/

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
