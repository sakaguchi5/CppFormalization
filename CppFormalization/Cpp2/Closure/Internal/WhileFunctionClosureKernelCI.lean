/- CppFormalization/Cpp2/Closure/Internal/WhileFunctionClosureKernelCI.lean -/
import CppFormalization.Cpp2.Closure.Function.FunctionBody
import CppFormalization.Cpp2.Closure.Package.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Legacy.Foundation.WhileEntryBoundaryCompatibilityCI
-- removed ideal relayout: import CppFormalization.Cpp2.Boundary.LoopBody.All  -- All.lean excluded
import CppFormalization.Cpp2.Closure.Internal.LoopBodyFunctionClosureCI
import CppFormalization.Cpp2.Stability.Closure.LoopReentryKernelCI
import CppFormalization.Cpp2.Operational.Divergence

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
        { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
          P.summary.returnOut = some out }

namespace LoopBodyReturnAdequacyProviderCI

/-- Preferred witness-facing name for the loop-body return provider. -/
def returnWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyReturnAdequacyProviderCI Γ σ body P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ body (.returnResult rv) σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
      P.summary.returnOut = some out } :=
  A.returnSound hstep

/-- Proof-only return soundness recovered from the witness provider. -/
theorem returnSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyReturnAdequacyProviderCI Γ σ body P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ body (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
      P.summary.returnOut = some out := by
  let w := A.returnWitness hstep
  exact ⟨w.val, w.property⟩

/-- Build a loop-body return provider from its witness-producing field. -/
def ofWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (returnWitness :
      ∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ body (.returnResult rv) σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
            P.summary.returnOut = some out }) :
    LoopBodyReturnAdequacyProviderCI Γ σ body P :=
  { returnSound := returnWitness }

end LoopBodyReturnAdequacyProviderCI

/--
A trivial return-adequacy provider when the chosen loop-body profile already
has a return channel.
-/
noncomputable def loopBodyReturnAdequacyProviderCI_of_returnOut
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (hout :
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
        P.summary.returnOut = some out) :
    LoopBodyReturnAdequacyProviderCI Γ σ body P :=
  LoopBodyReturnAdequacyProviderCI.ofWitness
    (returnWitness := by
      intro _rv _σ' _hstep
      exact ⟨Classical.choose hout, Classical.choose_spec hout⟩)

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
  LoopBodyReturnAdequacyProviderCI.ofWitness
    (returnWitness := by
      intro rv σ' hstep
      exact False.elim (hno (rv := rv) (σ' := σ') hstep))

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
    LoopBodyAdequacyCI Γ σ body hcurrent.toLoopBodyProfile :=
  LoopBodyAdequacyCI.ofWitness
    (normalWitness := by
      intro _σ' _hstep
      rcases hcurrent.toLoopBodyProfile.normalClosed with ⟨hN, hEq⟩
      exact ⟨⟨Γ, hN⟩, hEq⟩)
    (breakWitness := by
      intro _σ' _hstep
      rcases hcurrent.toLoopBodyProfile.breakClosed with ⟨hB, hEq⟩
      exact ⟨⟨Γ, hB⟩, hEq⟩)
    (continueWitness := by
      intro _σ' _hstep
      rcases hcurrent.toLoopBodyProfile.continueClosed with ⟨hC, hEq⟩
      exact ⟨⟨Γ, hC⟩, hEq⟩)
    (returnWitness := by
      intro rv σ' hstep
      exact hreturn.returnWitness hstep)

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
channel is not produced by the loop header itself. It is the body's `return`
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
        { outB : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
          (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry).toLoopBodyProfile.summary.returnOut =
            some outB }

/--
Residual exposure obligation for return-capable loop bodies.

This no longer performs the static projection to the body. It only says that
if the body actually returns at the current state, the top-level `while` static
profile has exposed a return channel. The conversion from that whole-`while`
return channel to the body return channel is handled separately by
`WhileLoopBodyReturnProfileProjectionCI`.
-/
structure WhileLoopBodyReturnExposureCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) : Type where
  exposeReturn :
    ∀ {rv : Option Value} {σ' : State},
      BigStepStmt σ body (.returnResult rv) σ' →
        { outW : {Δ : TypeEnv //
            HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ} //
          hentry.static.profile.summary.returnOut = some outW }

/--
Conditional exposure theorem for loop-body returns.

C++ reading:
if the while condition has evaluated to `true`, then an actual `return` from
the body is also an actual `return` from the whole `while` statement.
Therefore the top-level while adequacy exposes a return channel.

This theorem is deliberately conditional on `hcondTrue`. Without that premise,
a body return step does not imply that the while statement itself returns,
because the condition might evaluate to `false` and the body might not run.
-/
def whileLoopBodyReturnExposureCI_of_bodyClosureBoundaryCI_of_condTrue
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcondTrue : BigStepValue σ c (.bool true)) :
    WhileLoopBodyReturnExposureCI hentry := by
  refine { exposeReturn := ?_ }
  intro rv σ' hbodyReturn

  have hwhileReturn :
      BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ' :=
    BigStepStmt.whileTrueReturn hcondTrue hbodyReturn

  let w := hentry.adequacy.returnWitness hwhileReturn
  exact ⟨w.val, w.property⟩

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
  LoopBodyReturnAdequacyProviderCI.ofWitness
    (returnWitness := by
      intro rv σ' hstep
      let w := hexpose.exposeReturn hstep
      exact hproj.projectReturn (outW := w.val) w.property)

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
The loop-body return adequacy provider available once the current condition has
actually evaluated to `true`.

This is the theorem-backed replacement route for the return case of one
executed iteration.
-/
def loopBodyReturnAdequacyProviderCI_of_condTrue
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcondTrue : BigStepValue σ c (.bool true)) :
    LoopBodyReturnAdequacyProviderCI Γ σ body
      (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry).toLoopBodyProfile :=
  loopBodyReturnAdequacyProviderCI_of_staticProjection
    hentry
    (whileLoopBodyReturnProfileProjectionCI_of_bodyClosureBoundaryCI hentry)
    (whileLoopBodyReturnExposureCI_of_bodyClosureBoundaryCI_of_condTrue
      hentry hcondTrue)

/--
Condition-true loop-body boundary route.

Once the while condition has actually evaluated to `true`, the body is really
going to be executed. At that point the body-return exposure obligation is
theorem-backed by
`whileLoopBodyReturnExposureCI_of_bodyClosureBoundaryCI_of_condTrue`, so the
loop-body boundary can be assembled without the unconditional exposure shell.
-/
def whileLoopBoundaryCI_of_bodyClosureBoundaryCI_of_condTrue
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcondTrue : BigStepValue σ c (.bool true)) :
    LoopBodyBoundaryCI Γ σ body :=
  whileLoopBoundaryCI_of_entry_and_returnProvider
    hentry
    (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry)
    (loopBodyReturnAdequacyProviderCI_of_condTrue hentry hcondTrue)

/--
Condition-true local body progress/divergence.

This is the body-progress theorem that should be used inside the true branch of
a condition-first while proof. It avoids the unconditional
`whileLoopBodyReturnExposureCI_of_bodyClosureBoundaryCI` compatibility shell.
-/
theorem whileBodyProgressOrDiverges_of_bodyClosureBoundaryCI_of_condTrue
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcondTrue : BigStepValue σ c (.bool true)) :
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body := by
  exact
    loop_body_function_progress_or_diverges_ci
      (whileLoopBoundaryCI_of_bodyClosureBoundaryCI_of_condTrue hentry hcondTrue)

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

/-
LEGACY CURRENT-BOUNDARY BODY PROGRESS WRAPPER RETIRED

This wrapper went through the unconditional current-boundary loop-body route
retired above.  The condition-first replacement is
`whileBodyProgressOrDiverges_of_bodyClosureBoundaryCI_of_condTrue`.

Retired declaration:

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

-/

/--
A ready boolean while condition can evaluate to either `false` or `true`.

This is the condition-progress step needed before the while kernel can follow
the actual C++ execution order.
-/
theorem whileConditionEvalBool_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    BigStepValue σ c (.bool false) ∨ BigStepValue σ c (.bool true) := by
  let hcurrent : WhileEntryBoundaryCI Γ σ c body :=
    whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry
  rcases expr_ready_to_bigstep hcurrent.condReady with ⟨v, hv⟩
  have hcompat : ValueCompat v (.base .bool) :=
    expr_ready_eval_compat hcurrent.condReady hv
  cases hcompat
  rename_i b
  cases b
  · exact Or.inl hv
  · exact Or.inr hv

/--
Wrap a tail function-body result after one normal body iteration.
-/
theorem whileFunctionBody_of_tail_after_normal
    {σ σ1 σ2 : State} {c : ValExpr} {body : CppStmt} {ex : FunctionExit}
    (hcondTrue : BigStepValue σ c (.bool true))
    (hbodyNormal : BigStepStmt σ body .normal σ1)
    (htail : BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) :
    BigStepFunctionBody σ (.whileStmt c body) ex σ2 := by
  cases ex with
  | fellThrough =>
      have htailStmt : BigStepStmt σ1 (.whileStmt c body) .normal σ2 := by
        simpa using (BigStepFunctionBody.to_stmt htail)
      exact
        BigStepFunctionBody.fallthrough
          (BigStepStmt.whileTrueNormal hcondTrue hbodyNormal htailStmt)
  | returned rv =>
      have htailStmt : BigStepStmt σ1 (.whileStmt c body) (.returnResult rv) σ2 := by
        simpa using (BigStepFunctionBody.to_stmt htail)
      exact
        BigStepFunctionBody.returning
          (BigStepStmt.whileTrueNormal hcondTrue hbodyNormal htailStmt)

/--
Wrap a tail function-body result after one continue body iteration.
-/
theorem whileFunctionBody_of_tail_after_continue
    {σ σ1 σ2 : State} {c : ValExpr} {body : CppStmt} {ex : FunctionExit}
    (hcondTrue : BigStepValue σ c (.bool true))
    (hbodyContinue : BigStepStmt σ body .continueResult σ1)
    (htail : BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) :
    BigStepFunctionBody σ (.whileStmt c body) ex σ2 := by
  cases ex with
  | fellThrough =>
      have htailStmt : BigStepStmt σ1 (.whileStmt c body) .normal σ2 := by
        simpa using (BigStepFunctionBody.to_stmt htail)
      exact
        BigStepFunctionBody.fallthrough
          (BigStepStmt.whileTrueContinue hcondTrue hbodyContinue htailStmt)
  | returned rv =>
      have htailStmt : BigStepStmt σ1 (.whileStmt c body) (.returnResult rv) σ2 := by
        simpa using (BigStepFunctionBody.to_stmt htail)
      exact
        BigStepFunctionBody.returning
          (BigStepStmt.whileTrueContinue hcondTrue hbodyContinue htailStmt)

/--
Lift a tail closure result through a normal body iteration.
-/
theorem whileClosureResult_of_tail_after_normal
    {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    (hcondTrue : BigStepValue σ c (.bool true))
    (hbodyNormal : BigStepStmt σ body .normal σ1)
    (htail :
      (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
        BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ2, BigStepFunctionBody σ (.whileStmt c body) ex σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  cases htail with
  | inl hterm =>
      rcases hterm with ⟨ex, σ2, hfb⟩
      exact Or.inl
        ⟨ex, σ2,
          whileFunctionBody_of_tail_after_normal hcondTrue hbodyNormal hfb⟩
  | inr hdiv =>
      exact Or.inr
        (BigStepStmtDiv.whileIter hcondTrue (Or.inl hbodyNormal) hdiv)

/--
Lift a tail closure result through a continue body iteration.
-/
theorem whileClosureResult_of_tail_after_continue
    {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    (hcondTrue : BigStepValue σ c (.bool true))
    (hbodyContinue : BigStepStmt σ body .continueResult σ1)
    (htail :
      (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
        BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ2, BigStepFunctionBody σ (.whileStmt c body) ex σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  cases htail with
  | inl hterm =>
      rcases hterm with ⟨ex, σ2, hfb⟩
      exact Or.inl
        ⟨ex, σ2,
          whileFunctionBody_of_tail_after_continue hcondTrue hbodyContinue hfb⟩
  | inr hdiv =>
      exact Or.inr
        (BigStepStmtDiv.whileIter hcondTrue (Or.inr hbodyContinue) hdiv)

/--
Honest while case theorem.

This follows the C++ execution order:
1. evaluate the condition;
2. if false, the while falls through;
3. if true, execute the body;
4. body normal / continue re-enter the tail while;
5. body break falls through;
6. body return returns from the function body;
7. body divergence makes the whole while diverge.
-/
theorem while_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (_htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (_hloop : LoopBodyBoundaryCI Γ σ body)
    (hbodyClosure :
      (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body)
    (htailBoundary : WhileTailBoundaryKitCI Γ σ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  rcases whileConditionEvalBool_of_bodyClosureBoundaryCI hentry with hcondFalse | hcondTrue
  · exact Or.inl
      ⟨.fellThrough, σ,
        BigStepFunctionBody.fallthrough
          (BigStepStmt.whileFalse hcondFalse)⟩
  · cases hbodyClosure with
    | inr hbodyDiv =>
        exact Or.inr
          (BigStepStmtDiv.whileBody hcondTrue hbodyDiv)
    | inl hbodyTerm =>
        rcases hbodyTerm with ⟨ctrl, σ1, hbodyStep⟩
        cases ctrl with
        | normal =>
            exact
              whileClosureResult_of_tail_after_normal
                hcondTrue
                hbodyStep
                (htailClosure
                  (htailBoundary.afterNormal hcondTrue hbodyStep))
        | breakResult =>
            exact Or.inl
              ⟨.fellThrough, σ1,
                BigStepFunctionBody.fallthrough
                  (BigStepStmt.whileTrueBreak hcondTrue hbodyStep)⟩
        | continueResult =>
            exact
              whileClosureResult_of_tail_after_continue
                hcondTrue
                hbodyStep
                (htailClosure
                  (htailBoundary.afterContinue hcondTrue hbodyStep))
        | returnResult rv =>
            exact Or.inl
              ⟨.returned rv, σ1,
                BigStepFunctionBody.returning
                  (BigStepStmt.whileTrueReturn hcondTrue hbodyStep)⟩

/--
Residual provider for reconstructing the tail `while` boundary from a current
top-level while boundary.

This is deliberately smaller than a full `WhileTailBoundaryKitCI`:
- `reentry` reconstructs the post-state dynamic while entry after
  normal / continue body steps;
- `tailAdequacy` supplies the remaining post-state adequacy against the same
  static profile.

The actual `WhileTailBoundaryKitCI` is then assembled theoremically by
`whileTailBoundaryKitCI_of_loopReentry`.
-/
structure WhileTailBoundaryReentryProviderCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) : Type where
  reentry :
    LoopReentryKernelCI Γ c body
  tailAdequacy :
    WhileTailAdequacyProviderCI Γ σ c body hentry.static

/--
Residual delimiter-reentry shell for the canonical boundary route.

This is only the reentry law:
after a normal / continue body step, the condition and local loop-body boundary
can be replayed at the post-state.
-/
axiom loopReentryKernelCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopReentryKernelCI Γ c body

/--
Residual post-state adequacy shell for the canonical boundary route.

This is separate from reentry. Reentry supplies the dynamic tail entry;
this provider supplies adequacy of the tail while against the unchanged static
profile after normal / continue body steps.
-/
axiom whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailAdequacyProviderCI Γ σ c body hentry.static

/--
Compatibility provider assembled from the two smaller residual obligations.

This keeps the previous provider name available, but it is no longer an atomic
shell.
-/
noncomputable def whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailBoundaryReentryProviderCI hentry :=
  { reentry :=
      loopReentryKernelCI_of_bodyClosureBoundaryCI hentry
    tailAdequacy :=
      whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry }

/--
Condition-first while closure using the reentry-provider route.

This is the clean mainline theorem for `while`:
- evaluate the condition first;
- in the false branch, no loop-body boundary is needed;
- in the true branch, assemble the loop-body boundary using the condition-true
  return-exposure theorem;
- assemble the tail-boundary kit from reentry + post-state adequacy.

Therefore this theorem avoids both compatibility shortcuts:
- unconditional loop-body return exposure;
- direct tail-boundary kit extraction.
-/
theorem while_function_body_closure_boundary_ci_of_reentryProvider_condition_first
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (P : WhileTailBoundaryReentryProviderCI hentry)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  rcases whileConditionEvalBool_of_bodyClosureBoundaryCI hentry with hcondFalse | hcondTrue
  · exact Or.inl
      ⟨.fellThrough, σ,
        BigStepFunctionBody.fallthrough
          (BigStepStmt.whileFalse hcondFalse)⟩
  · let hloop : LoopBodyBoundaryCI Γ σ body :=
      whileLoopBoundaryCI_of_bodyClosureBoundaryCI_of_condTrue hentry hcondTrue
    let hbodyClosure :
        (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body :=
      loop_body_function_progress_or_diverges_ci hloop
    let htailBoundary : WhileTailBoundaryKitCI Γ σ c body :=
      whileTailBoundaryKitCI_of_loopReentry
        hentry
        (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry)
        hloop
        P.reentry
        P.tailAdequacy
    exact
      while_function_body_closure_boundary_ci_honest
        htyWhile
        hentry
        hloop
        hbodyClosure
        htailBoundary
        htailClosure

end Cpp
