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
- loop-body local boundary は、entry から読める structural/profile/dynamic と、
  body return channel adequacy へ分解する。
- tail-boundary reconstruction は、まだ別責務として残す。
- `LoopReentryKernelCI` は tail `while` の dynamic entry を再構成する mechanism である。
- tail `while` の full `BodyClosureBoundaryCI` には、dynamic だけでなく
  top-level while adequacy at post-state が必要なので、それを明示的な
  `WhileTailAdequacyProviderCI` として分ける。
- これにより、reentry law と adequacy obligation を混ぜない。
- さらに、loop-body boundary 全体を axiom にせず、
  残る未証明責務を body return adequacy provider へ縮める。
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
The remaining local adequacy obligation needed to view the `while` body as a
4-channel loop body.

For `normal` / `break` / `continue`, `WhileEntryBoundaryCI.toLoopBodyProfile`
already carries closed-at-entry witnesses, so the loop-body adequacy proof can
return those witnesses directly.

Only `return` is path-sensitive:
if the body actually returns, the loop-body profile must expose the
corresponding body-return channel.  This provider is the precise residual
obligation replacing the older whole-boundary shell.
-/
structure LoopBodyReturnAdequacyProviderCI
    (Γ : TypeEnv) (σ : State) (body : CppStmt)
    (P : LoopBodyControlProfile Γ body) : Type where
  returnSound :
    ∀ {rv : Option Value} {σ' : State},
      BigStepStmt σ body (.returnResult rv) σ' →
        ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
          P.summary.returnOut = some out

/--
A trivial return-adequacy provider when the chosen loop-body profile already
has a return channel.
-/
def loopBodyReturnAdequacyProviderCI_of_returnOut
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (hout :
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
        P.summary.returnOut = some out) :
    LoopBodyReturnAdequacyProviderCI Γ σ body P :=
  { returnSound := by
      intro _rv _σ' _hstep
      exact hout }

/--
A return-adequacy provider when body returns are semantically excluded.
-/
def loopBodyReturnAdequacyProviderCI_of_noReturn
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (hno :
      ∀ {rv : Option Value} {σ' : State},
        ¬ BigStepStmt σ body (.returnResult rv) σ') :
    LoopBodyReturnAdequacyProviderCI Γ σ body P :=
  { returnSound := by
      intro rv σ' hstep
      exact False.elim (hno (rv := rv) (σ' := σ') hstep) }

/--
Loop-body structural boundary projected from the top-level `while` structural
boundary.

A top-level well-scoped `while` means its body is well-scoped one loop deeper;
that is exactly `BreakWellScopedInLoop` / `ContinueWellScopedInLoop`.
-/
def whileLoopBodyStructuralBoundaryCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopBodyStructuralBoundary Γ body := by
  refine
    { wf := ?_
      breakScoped := ?_
      continueScoped := ?_ }
  · have hwf : WellFormedValue c ∧ WellFormedStmt body := by
      simpa [WellFormedStmt] using hentry.structural.wf
    exact hwf.2
  · simpa [BreakWellScoped, BreakWellScopedInLoop] using hentry.structural.breakScoped
  · simpa [ContinueWellScoped, ContinueWellScopedInLoop] using hentry.structural.continueScoped

/--
Loop-body adequacy assembled from the entry-projected loop profile plus the
remaining return-channel provider.

This theorem is the main payoff of the split:
normal / break / continue adequacy are no longer obligations.
-/
def loopBodyAdequacyCI_of_entry_and_returnProvider
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hcurrent : WhileEntryBoundaryCI Γ σ c body)
    (hreturn :
      LoopBodyReturnAdequacyProviderCI Γ σ body hcurrent.toLoopBodyProfile) :
    LoopBodyAdequacyCI Γ σ body hcurrent.toLoopBodyProfile := by
  refine
    { normalSound := ?_
      breakSound := ?_
      continueSound := ?_
      returnSound := ?_ }
  · intro _σ' _hstep
    rcases hcurrent.toLoopBodyProfile.normalClosed with ⟨hN, hEq⟩
    exact ⟨⟨Γ, hN⟩, hEq⟩
  · intro _σ' _hstep
    rcases hcurrent.toLoopBodyProfile.breakClosed with ⟨hB, hEq⟩
    exact ⟨⟨Γ, hB⟩, hEq⟩
  · intro _σ' _hstep
    rcases hcurrent.toLoopBodyProfile.continueClosed with ⟨hC, hEq⟩
    exact ⟨⟨Γ, hC⟩, hEq⟩
  · intro rv σ' hstep
    exact hreturn.returnSound hstep

/--
Assemble the loop-body boundary from:
- top-level while structural information,
- theorem-backed current-entry information,
- the remaining body-return adequacy provider.

This is the explicit route new code should use.
-/
def whileLoopBoundaryCI_of_entry_and_returnProvider
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcurrent : WhileEntryBoundaryCI Γ σ c body)
    (hreturn :
      LoopBodyReturnAdequacyProviderCI Γ σ body hcurrent.toLoopBodyProfile) :
    LoopBodyBoundaryCI Γ σ body :=
  { structural :=
      whileLoopBodyStructuralBoundaryCI_of_bodyClosureBoundaryCI hentry
    profile := hcurrent.toLoopBodyProfile
    dynamic := hcurrent.toLoopBodyDynamic
    adequacy :=
      loopBodyAdequacyCI_of_entry_and_returnProvider hcurrent hreturn }

/--
Static projection from the top-level `while` return profile to the local
loop-body return profile.

C++ reading: if the `while` statement has a static `return` channel, that
channel is not produced by the loop header itself.  It is the body's `return`
channel lifted through the `while_return` typing rule.

This object is deliberately state-free except for its reference to the assembled
boundary whose static profile is being projected.
-/
structure WhileLoopBodyReturnProfileProjectionCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) : Type where
  projectReturn :
    ∀ {outW : {Δ : TypeEnv //
        HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ}},
      hentry.static.profile.summary.returnOut = some outW →
        ∃ outB : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
          (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry).toLoopBodyProfile.summary.returnOut =
            some outB

/--
Residual exposure obligation for return-capable loop bodies.

This no longer performs the static projection to the body.  It only says that
if the body actually returns at the current state, the top-level `while` static
profile has exposed a return channel.  The conversion from that whole-`while`
return channel to the body return channel is handled separately by
`WhileLoopBodyReturnProfileProjectionCI`.
-/
structure WhileLoopBodyReturnExposureCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) : Type where
  exposeReturn :
    ∀ {rv : Option Value} {σ' : State},
      BigStepStmt σ body (.returnResult rv) σ' →
        ∃ outW : {Δ : TypeEnv //
            HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ},
          hentry.static.profile.summary.returnOut = some outW

/--
Build the old local return-adequacy provider from the cleaner two-part split:
1. expose a whole-`while` return channel when the body actually returns;
2. project that whole-`while` return channel to the body return channel.
-/
def loopBodyReturnAdequacyProviderCI_of_staticProjection
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hproj : WhileLoopBodyReturnProfileProjectionCI hentry)
    (hexpose : WhileLoopBodyReturnExposureCI hentry) :
    LoopBodyReturnAdequacyProviderCI Γ σ body
      (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry).toLoopBodyProfile :=
  { returnSound := by
      intro rv σ' hstep
      rcases hexpose.exposeReturn hstep with ⟨outW, hW⟩
      exact hproj.projectReturn hW }

/--
Static projection for the canonical boundary route.

A whole-`while` return profile entry is the lifted body return profile entry.
This is purely static: it only unfolds the `while_return` typing payload via
`while_return_typing_data` and the entry-projected loop-body profile.
-/
def whileLoopBodyReturnProfileProjectionCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileLoopBodyReturnProfileProjectionCI hentry := by
  refine { projectReturn := ?_ }
  intro outW hW
  refine ⟨⟨outW.1, ?_⟩, ?_⟩
  · exact (while_return_typing_data outW.2).2.2.2
  · exact
      whileEntryBoundaryCI_toLoopBodyProfile_returnOut_of_static
        hentry hW
/--
Dynamic residual shell for the canonical boundary route after the static split.

Compared with the former return-adequacy provider, this no longer needs to know
how to convert a whole-`while` return typing payload into a body return typing
payload.  It only exposes that the static profile contains a return channel
when the body can actually return.
-/
axiom whileLoopBodyReturnExposureCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileLoopBodyReturnExposureCI hentry

/--
Compatibility wrapper for existing callers.

The old residual provider is now a `def`, assembled from the static return
projection plus the smaller dynamic exposure obligation.
-/
def loopBodyReturnAdequacyProviderCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopBodyReturnAdequacyProviderCI Γ σ body
      (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry).toLoopBodyProfile :=
  loopBodyReturnAdequacyProviderCI_of_staticProjection
    hentry
    (whileLoopBodyReturnProfileProjectionCI_of_bodyClosureBoundaryCI hentry)
    (whileLoopBodyReturnExposureCI_of_bodyClosureBoundaryCI hentry)

/--
Current iteration の loop-body local boundary extracted from a top-level `while`
closure boundary.

This is no longer an opaque boundary axiom.  It is assembled from:
- structural projection from the top-level while boundary;
- current-entry projection via `whileEntryBoundaryCI_of_bodyClosureBoundaryCI`;
- the smaller residual return-adequacy provider above.
-/
def whileLoopBoundaryCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopBodyBoundaryCI Γ σ body :=
  whileLoopBoundaryCI_of_entry_and_returnProvider
    hentry
    (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry)
    (loopBodyReturnAdequacyProviderCI_of_bodyClosureBoundaryCI hentry)

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
