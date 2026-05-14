import CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Typing.ControlProfile

namespace Cpp

/-!
# Closure.Foundation.LoopBodyBoundaryCI

`while` body 専用の 4-channel boundary.

狙い:
- top-level function body 用の `Body*` boundary から、loop body の責務を分離する。
- loop body では `break` / `continue` は未解決な top-level abrupt ではなく、
  enclosing `while` が捕捉する合法な local exit である。
- したがって top-level body の 2-channel (`normal` / `return`) profile を流用せず、
  body-local な 4-channel contract を独立に持つ。

このファイルは foundation 側の静的/動的/adequacy vocabulary を置く。
while header に再入する法則は `LoopReentryKernelCI` 側へ分離する。

2026-05 witness-provider patch:
- `LoopBodyAdequacyCI` is now witness-producing at the primitive field level.
- The historical projection names `normalSound` / `breakSound` /
  `continueSound` / `returnSound` are kept source-compatible, but their result
  is now a subtype witness rather than a proof-only existential.
- New witness-facing aliases `normalWitness` / `breakWitness` /
  `continueWitness` / `returnWitness` are provided in the namespace.
- Proof-only existential surfaces are recovered by namespace theorems
  `normalSoundExists` / `breakSoundExists` / `continueSoundExists` /
  `returnSoundExists`.
-/

/-- `while` body を 1 段ぶん loop の内側で読むための break scopedness。 -/
abbrev BreakWellScopedInLoop (st : CppStmt) : Prop :=
  BreakWellScopedAt 1 st

/-- `while` body を 1 段ぶん loop の内側で読むための continue scopedness。 -/
abbrev ContinueWellScopedInLoop (st : CppStmt) : Prop :=
  ContinueWellScopedAt 1 st

/--
loop body の 4-channel summary.

`normal` / `break` / `continue` も `return` と同様に option で持つが、
`LoopBodyControlProfile` 側で while-compatible な closed-at-start witness を
明示的に要求する。
-/
structure LoopBodySummary (Γ : TypeEnv) (body : CppStmt) : Type where
  normalOut : Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ}
  breakOut : Option {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ}
  continueOut : Option {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ}
  returnOut : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ}

/--
state-independent structural boundary for a single `while` body.

ここでは top-level body と違って `break` / `continue` を禁止しない。
代わりに「今まさに 1 段の loop の内側にいる」ことを scopedness に反映する。
-/
structure LoopBodyStructuralBoundary (Γ : TypeEnv) (body : CppStmt) : Prop where
  wf : WellFormedStmt body
  breakScoped : BreakWellScopedInLoop body
  continueScoped : ContinueWellScopedInLoop body

/--
state-free 4-channel control profile for a loop body.

current CI typing では enclosing `while` が body に対して
- `normalK Γ body Γ`
- `breakK Γ body Γ`
- `continueK Γ body Γ`
を要求するので、その closed-at-start witness を profile の一部として固定する。
`return` だけは path-sensitive に残す。
-/
structure LoopBodyControlProfile (Γ : TypeEnv) (body : CppStmt) : Type where
  summary : LoopBodySummary Γ body
  normalClosed :
    { h : HasTypeStmtCI .normalK Γ body Γ //
      summary.normalOut = some ⟨Γ, h⟩ }
  breakClosed :
    { h : HasTypeStmtCI .breakK Γ body Γ //
      summary.breakOut = some ⟨Γ, h⟩ }
  continueClosed :
    { h : HasTypeStmtCI .continueK Γ body Γ //
      summary.continueOut = some ⟨Γ, h⟩ }

/-- state-dependent entry boundary for a loop body. -/
structure LoopBodyDynamicBoundary (Γ : TypeEnv) (σ : State) (body : CppStmt) : Prop where
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ body

/--
Adequacy of a loop-body 4-channel profile against actual statement execution.

The primitive fields are now witness-producing.  The names are kept as the
historical `*Sound` projections for source compatibility with existing record
literals, but each projection returns the concrete selected output channel as
data:

`{ out // P.summary.<channel> = some out }`.

Use the namespace aliases `normalWitness`, `breakWitness`, `continueWitness`,
and `returnWitness` when writing new code.
-/
structure LoopBodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (body : CppStmt)
    (P : LoopBodyControlProfile Γ body) : Type where
  normalSound :
    ∀ {σ' : State},
      BigStepStmt σ body .normal σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ} //
          P.summary.normalOut = some out }

  breakSound :
    ∀ {σ' : State},
      BigStepStmt σ body .breakResult σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ} //
          P.summary.breakOut = some out }

  continueSound :
    ∀ {σ' : State},
      BigStepStmt σ body .continueResult σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ} //
          P.summary.continueOut = some out }

  returnSound :
    ∀ {rv : Option Value} {σ' : State},
      BigStepStmt σ body (.returnResult rv) σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
          P.summary.returnOut = some out }

namespace LoopBodyAdequacyCI

/-- Witness-producing normal adequacy, preferred name for new code. -/
def normalWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .normal σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ} //
      P.summary.normalOut = some out } :=
  A.normalSound hstep

/-- Witness-producing break adequacy, preferred name for new code. -/
def breakWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .breakResult σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ} //
      P.summary.breakOut = some out } :=
  A.breakSound hstep

/-- Witness-producing continue adequacy, preferred name for new code. -/
def continueWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .continueResult σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ} //
      P.summary.continueOut = some out } :=
  A.continueSound hstep

/-- Witness-producing return adequacy, preferred name for new code. -/
def returnWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ body (.returnResult rv) σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
      P.summary.returnOut = some out } :=
  A.returnSound hstep

/-- Proof-only normal soundness recovered from the witness provider. -/
theorem normalSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ},
      P.summary.normalOut = some out := by
  let w := A.normalWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only break soundness recovered from the witness provider. -/
theorem breakSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .breakResult σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ},
      P.summary.breakOut = some out := by
  let w := A.breakWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only continue soundness recovered from the witness provider. -/
theorem continueSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .continueResult σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ},
      P.summary.continueOut = some out := by
  let w := A.continueWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only return soundness recovered from the witness provider. -/
theorem returnSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ body (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
      P.summary.returnOut = some out := by
  let w := A.returnWitness hstep
  exact ⟨w.val, w.property⟩

/-- Build loop-body adequacy from primitive witness-producing fields. -/
def ofWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (normalWitness :
      ∀ {σ' : State},
        BigStepStmt σ body .normal σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ} //
            P.summary.normalOut = some out })
    (breakWitness :
      ∀ {σ' : State},
        BigStepStmt σ body .breakResult σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ} //
            P.summary.breakOut = some out })
    (continueWitness :
      ∀ {σ' : State},
        BigStepStmt σ body .continueResult σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ} //
            P.summary.continueOut = some out })
    (returnWitness :
      ∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ body (.returnResult rv) σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
            P.summary.returnOut = some out }) :
    LoopBodyAdequacyCI Γ σ body P :=
  { normalSound := normalWitness
    breakSound := breakWitness
    continueSound := continueWitness
    returnSound := returnWitness }

/--
Build loop-body adequacy from the old proof-only surfaces.

This is intentionally `noncomputable`: it uses classical choice to convert
proof-only existentials into subtype witnesses.  New code should prefer
`ofWitness`; this helper is only for migration.
-/
noncomputable def ofSound
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (normalSound :
      ∀ {σ' : State},
        BigStepStmt σ body .normal σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ},
            P.summary.normalOut = some out)
    (breakSound :
      ∀ {σ' : State},
        BigStepStmt σ body .breakResult σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ},
            P.summary.breakOut = some out)
    (continueSound :
      ∀ {σ' : State},
        BigStepStmt σ body .continueResult σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ},
            P.summary.continueOut = some out)
    (returnSound :
      ∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ body (.returnResult rv) σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
            P.summary.returnOut = some out) :
    LoopBodyAdequacyCI Γ σ body P :=
  { normalSound := by
      intro σ' hstep
      let h := normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    breakSound := by
      intro σ' hstep
      let h := breakSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    continueSound := by
      intro σ' hstep
      let h := continueSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    returnSound := by
      intro rv σ' hstep
      let h := returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩ }

end LoopBodyAdequacyCI

/-- assembled 4-layer boundary for a single `while` body. -/
structure LoopBodyBoundaryCI (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  structural : LoopBodyStructuralBoundary Γ body
  profile : LoopBodyControlProfile Γ body
  dynamic : LoopBodyDynamicBoundary Γ σ body
  adequacy : LoopBodyAdequacyCI Γ σ body profile

/-- constructor-style helper mirroring `mkBodyClosureBoundaryCI`. -/
def mkLoopBodyBoundaryCI
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (hs : LoopBodyStructuralBoundary Γ body)
    (hp : LoopBodyControlProfile Γ body)
    (hd : LoopBodyDynamicBoundary Γ σ body)
    (ha : LoopBodyAdequacyCI Γ σ body hp) :
    LoopBodyBoundaryCI Γ σ body :=
  { structural := hs
    profile := hp
    dynamic := hd
    adequacy := ha }

end Cpp
