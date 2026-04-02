import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Lemmas.ControlExclusion

namespace Cpp

/-!
# Closure.Foundation.BodyBoundaryCI

Legacy CI-boundary wrapper.

役割:
- old `BodyReadyCI` / `BlockBodyReadyCI` は compatibility surface として残す。
- control summary の primitive definitions (`BodyExitKind`, `StmtBodySummary`, `BlockBodySummary`)
  は canonical foundation へ移したので、ここでは再定義しない。
-/

structure BodyReadyCI (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  wf : WellFormedStmt st
  typed0 : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ st
  summary : StmtBodySummary Γ st
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepStmt σ st .normal σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
        summary.normalOut = some out
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepStmt σ st (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
        summary.returnOut = some out

structure BlockBodyReadyCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  wf : WellFormedBlock ss
  typed0 : ∃ Δ, HasTypeBlock (pushTypeScope Γ) ss Δ
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss
  state : ScopedTypedStateConcrete (pushTypeScope Γ) σ
  safe : BlockReadyConcrete (pushTypeScope Γ) σ ss
  summary : BlockBodySummary Γ ss
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
      ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ},
        summary.normalOut = some out
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ},
        summary.returnOut = some out

theorem break_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .breakResult σ' := by
  intro σ' hstep
  exact stmt_break_not_scoped hstep h.breakScoped

theorem continue_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .continueResult σ' := by
  intro σ' hstep
  exact stmt_continue_not_scoped hstep h.continueScoped

theorem top_level_abrupt_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyReadyCI Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact stmt_break_not_scoped hbreak hready.breakScoped
  · intro hcont
    exact stmt_continue_not_scoped hcont hready.continueScoped

theorem top_level_abrupt_excluded_from_blockBodyReadyCI
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyReadyCI Γ σ ss →
    ¬ BigStepBlock σ ss .breakResult σ' ∧ ¬ BigStepBlock σ ss .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact no_top_break_from_scoped_block hready.breakScoped hbreak
  · intro hcont
    exact no_top_continue_from_scoped_block hready.continueScoped hcont

end Cpp
