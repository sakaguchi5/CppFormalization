/- CppFormalization/Cpp2/Closure/Internal/WhileFunctionClosureKernelCI.lean -/
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.WhileEntryBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.LoopBodyFunctionClosureCI
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.WhileFunctionClosureKernelCI

Honest kernel surface for `while` function-body closure.

設計意図:
- `while` 全体の closure と、1 iteration の loop-body local closure を分離する。
- current-entry で読める事実は `WhileEntryBoundaryCI` から theorem-backed に読む。
- loop-body local boundary と tail-boundary reconstruction は、まだ別責務として残す。
- `LoopReentryKernelCI` は tail `while` の dynamic entry を再構成する mechanism である。
- tail `while` の full `BodyClosureBoundaryCI` には、dynamic だけでなく
  top-level while adequacy at post-state が必要なので、それを明示的な
  `WhileTailAdequacyProviderCI` として分ける。
- これにより、reentry law と adequacy obligation を混ぜない。
-/

/--
Normal / continue の 1 iteration 後に、tail `while` の top-level closure boundary を
再構成するための kit.
-/
structure WhileTailBoundaryKitCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  afterNormal :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .normal σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)
  afterContinue :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .continueResult σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)

/--
Tail `while` の post-state adequacy obligation.

`LoopReentryKernelCI` が供給するのは post-state dynamic entry までである。
full `BodyClosureBoundaryCI` を作るには、同じ static profile に対する
post-state adequacy が別途必要になる。これをここで明示する。
-/
structure WhileTailAdequacyProviderCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt)
    (static : BodyStaticBoundaryCI Γ (.whileStmt c body)) : Type where
  afterNormal :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .normal σ1 →
      BodyAdequacyCI Γ σ1 (.whileStmt c body) static.profile
  afterContinue :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .continueResult σ1 →
      BodyAdequacyCI Γ σ1 (.whileStmt c body) static.profile

/--
Build a full tail-boundary kit from:
- the current top-level while boundary, which supplies structural/static data;
- the theorem-backed current entry, which supplies condition readiness;
- the current loop-body local boundary;
- the delimiter reentry kernel, which supplies post-state dynamic readiness;
- the explicit post-state adequacy provider.

This is the honest decomposition of tail-boundary reconstruction.
-/
def whileTailBoundaryKitCI_of_loopReentry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcurrent : WhileEntryBoundaryCI Γ σ c body)
    (hloop : LoopBodyBoundaryCI Γ σ body)
    (hreentry : LoopReentryKernelCI Γ c body)
    (hadequacy : WhileTailAdequacyProviderCI Γ σ c body hentry.static) :
    WhileTailBoundaryKitCI Γ σ c body := by
  refine
    { afterNormal := ?_
      afterContinue := ?_ }
  · intro σ1 hcondTrue hstep
    exact
      { structural := hentry.structural
        static := hentry.static
        dynamic :=
          LoopReentryKernelCI.whileDynamic_after_normal
            hreentry
            hcurrent.condReady
            hloop
            hstep
        adequacy := hadequacy.afterNormal hcondTrue hstep }
  · intro σ1 hcondTrue hstep
    exact
      { structural := hentry.structural
        static := hentry.static
        dynamic :=
          LoopReentryKernelCI.whileDynamic_after_continue
            hreentry
            hcurrent.condReady
            hloop
            hstep
        adequacy := hadequacy.afterContinue hcondTrue hstep }

/--
Current-entry typing read directly from the theorem-backed `WhileEntryBoundaryCI`.

This is no longer a shell: the static-layer redesign makes the while header
typing data available from `BodyClosureBoundaryCI.static`.
-/
theorem whileTypingCI_of_whileEntryBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : WhileEntryBoundaryCI Γ σ c body) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ := by
  exact HasTypeStmtCI.while_normal hentry.hc hentry.hN hentry.hB hentry.hC

/--
Current-entry typing extracted from a top-level `while` closure boundary.

This is the first payoff of the `BodyStaticBoundaryCI` redesign:
the old axiom is now a theorem.
-/
theorem whileTypingCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ := by
  intro h
  exact whileTypingCI_of_whileEntryBoundaryCI
    (whileEntryBoundaryCI_of_bodyClosureBoundaryCI h)

/--
Current iteration の loop-body local boundary extracted from a top-level `while`
closure boundary.

This remains a real obligation.  The current entry gives only:
- condition typing/readiness,
- body normal/break/continue typing,
- current body readiness.

It does **not** by itself provide the 4-channel loop-body adequacy required by
`LoopBodyBoundaryCI`.
-/
axiom whileLoopBoundaryCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    LoopBodyBoundaryCI Γ σ body

/--
Local body progress/divergence extracted from a top-level `while` closure boundary.

これは独立な shell ではなく、loop-body boundary からの導出として置く。
-/
theorem whileBodyProgressOrDiverges_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body := by
  intro hentry
  exact
    loop_body_function_progress_or_diverges_ci
      (whileLoopBoundaryCI_of_bodyClosureBoundaryCI hentry)

/--
Tail-boundary reconstruction shell extracted from a top-level `while` closure boundary.

normal / continue の 1 iteration 後に、tail `while` へ渡す top-level closure
boundary を再構成する責務だけを分離する。

New code should prefer `whileTailBoundaryKitCI_of_loopReentry`, which exposes
the delimiter reentry kernel and the remaining post-state adequacy obligation
separately.  This compatibility shell remains only for the current boundary
route.
-/
axiom whileTailBoundaryKitCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileTailBoundaryKitCI Γ σ c body

/--
Honest while case theorem.

必要なものを明示する:
- current entry の top-level closure boundary
- current iteration の loop-body local boundary
- current iteration 自身の local progress/divergence
- normal / continue 後の tail-boundary reconstruction
- tail `while` そのものの recursive closure hypothesis
-/
axiom while_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body)
    (hbodyClosure :
      (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body)
    (htailBoundary : WhileTailBoundaryKitCI Γ σ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body)

end Cpp
