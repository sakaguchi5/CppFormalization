import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Lemmas.ControlExclusion






namespace Cpp

/-!
# Closure.Foundation.BodyBoundaryCI

internal closure kernel が直接使う CI-centric boundary contract.
old `BodyReady` は coarse external boundary として残し、
ここでは control-sensitive な static summary を明示的に持つ。
-/

/-- function-body top level で観測したい出口 channel. -/
inductive BodyExitKind where
  | normal
  | returned
  deriving DecidableEq, Repr

/--
statement 用の internal control summary.
`Δ` は mere existence ではなく channel payload の一部として保持する。
-/
structure StmtBodySummary (Γ : TypeEnv) (st : CppStmt) : Type where
  normalOut : Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}
  returnOut : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}

/--
opened block body 用の internal control summary.
block-body は `pushTypeScope Γ` 下で見る。
-/
structure BlockBodySummary (Γ : TypeEnv) (ss : StmtBlock) : Type where
  normalOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ}
  returnOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ}

/--
CI-oriented function-body boundary contract.

意図:
- coarse old typing は provenance としては残してよいが、internal kernel の主役にはしない。
- actual step ごとに witness を生成する関数ではなく、
  先に static summary を持ち、その adequacy を別 field で述べる。
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

/--
CI-oriented opened block-body boundary contract.

`BlockBodyReadyCI` は `BodyReadyCI` のコピーではなく、
opened scope 下の block-body 用 boundary として独立に持つ。
-/
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

/-- top-level function-body では unresolved break は起きない。-/
theorem break_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .breakResult σ' := by
  intro σ' hstep
  exact stmt_break_not_scoped hstep h.breakScoped

/-- top-level function-body では unresolved continue は起きない。-/
theorem continue_excluded_from_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .continueResult σ' := by
  intro σ' hstep
  exact stmt_continue_not_scoped hstep h.continueScoped





/-- Top-level abrupt control is excluded at a CI function-body boundary as well. -/
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

/-- Opened block-body boundaries exclude unresolved abrupt exits. -/
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
