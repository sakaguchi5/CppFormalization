import CppFormalization.Cpp2.Boundary.Body.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.Safety.Facts.ControlExclusion

namespace Cpp

/-!
# Body closure boundary control-exclusion facts

Semantic consequences of a full body boundary and structural scopedness.

The boundary object itself lives in `Boundary.Body.BodyClosureBoundaryCI`; these
facts are separated because they connect that boundary to big-step execution.
-/

theorem break_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .breakResult σ' := by
  intro σ' hstep
  exact stmt_break_not_scoped hstep h.structural.breakScoped

theorem continue_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .continueResult σ' := by
  intro σ' hstep
  exact stmt_continue_not_scoped hstep h.structural.continueScoped

theorem top_level_abrupt_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyClosureBoundaryCI Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro h
  constructor
  · exact break_excluded_from_bodyClosureBoundaryCI h
  · exact continue_excluded_from_bodyClosureBoundaryCI h

theorem top_level_abrupt_excluded_from_blockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss →
    ¬ BigStepBlock σ ss .breakResult σ' ∧ ¬ BigStepBlock σ ss .continueResult σ' := by
  intro h
  constructor
  · intro hbreak
    exact no_top_break_from_scoped_block h.structural.breakScoped hbreak
  · intro hcont
    exact no_top_continue_from_scoped_block h.structural.continueScoped hcont


end Cpp
