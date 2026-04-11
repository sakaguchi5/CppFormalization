import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile

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
    ∃ h : HasTypeStmtCI .normalK Γ body Γ,
      summary.normalOut = some ⟨Γ, h⟩
  breakClosed :
    ∃ h : HasTypeStmtCI .breakK Γ body Γ,
      summary.breakOut = some ⟨Γ, h⟩
  continueClosed :
    ∃ h : HasTypeStmtCI .continueK Γ body Γ,
      summary.continueOut = some ⟨Γ, h⟩

/-- state-dependent entry boundary for a loop body. -/
structure LoopBodyDynamicBoundary (Γ : TypeEnv) (σ : State) (body : CppStmt) : Prop where
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ body

/--
adequacy of a loop-body 4-channel profile against actual statement execution.

`normal` / `break` / `continue` は closed-at-start witness が profile に固定されているが、
actual big-step exit がその channel によって代表されることを adequacy として別に持つ。
-/
structure LoopBodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (body : CppStmt)
    (P : LoopBodyControlProfile Γ body) : Type where
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepStmt σ body .normal σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ},
        P.summary.normalOut = some out
  breakSound :
    ∀ {σ' : State} (_hstep : BigStepStmt σ body .breakResult σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ},
        P.summary.breakOut = some out
  continueSound :
    ∀ {σ' : State} (_hstep : BigStepStmt σ body .continueResult σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ},
        P.summary.continueOut = some out
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepStmt σ body (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
        P.summary.returnOut = some out

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
