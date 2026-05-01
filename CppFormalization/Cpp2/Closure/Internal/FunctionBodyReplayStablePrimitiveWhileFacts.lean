import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyWitnessCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyPrimitiveClosureCI
import CppFormalization.Cpp2.Closure.Internal.WhileBodyClassCI
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReplayStablePrimitiveFacts
import CppFormalization.Cpp2.Boundary.FunctionBody

namespace Cpp

/-!
# Closure.Internal.FunctionBodyReplayStablePrimitiveWhileFacts

Replay-stable primitive `while` bodies give a theorem-backed reentry support
surface for function-body closure.

This file is now routed through the honest decomposition:
- loop-body local boundary remains explicit;
- delimiter reentry is provided by `LoopReentryKernelCI`;
- post-state top-level while adequacy is provided separately by
  `WhileTailAdequacyProviderCI`;
- the old direct `WhileTailBoundaryKitCI` construction is retained only as a
  compatibility projection from the reentry-based support.

Witness-provider migration:
- add a witness-producing tail adequacy provider in parallel with the existing
  proof-only provider;
- keep the existing proof-only route source-compatible;
- expose replay-stable primitive while tail adequacy as `BodyAdequacyWitnessCI`
  so the final `BodyAdequacyCI` provider replacement has a local landing zone.
-/

/-! ## theorem-backed replay-stable primitive while tail boundary -/

/-- replay-stable primitive 文は raw return を起こさない。 -/
theorem replay_stable_primitive_stmt_no_return
    {σ σ' : State} {st : CppStmt} {rv : Option Value} :
    ReplayStablePrimitiveStmt st →
    ¬ BigStepStmt σ st (.returnResult rv) σ' := by
  intro hstable hret
  cases st <;> simp [ReplayStablePrimitiveStmt] at hstable <;> cases hret

/--
導出 recursor で while-return を直接潰す補助 claim。
while 以外の statement については `True` に落としているので、
興味のある while-return case だけが本気の branch になる。
-/
private theorem replay_stable_while_return_claim
    {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ s ctrl σ') :
    match s, ctrl with
    | .whileStmt _ body, .returnResult _ => ReplayStablePrimitiveStmt body → False
    | _, _ => True := by
  exact
    BigStepStmt.rec
      (motive_1 := fun {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
        (h : BigStepStmt σ s ctrl σ') =>
          match s, ctrl with
          | .whileStmt _ body, .returnResult _ => ReplayStablePrimitiveStmt body → False
          | _, _ => True)
      (motive_2 := fun {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
        (_h : BigStepBlock σ ss ctrl σ') => True)
      (skip := by intro σ; trivial)
      (expr := by intro σ e v hval; trivial)
      (assign := by intro σ σ' p e v hval hassign; trivial)
      (declareObjNone := by intro σ σ' τ x hdecl; trivial)
      (declareObjSome := by intro σ σ' τ x e v hval hdecl; trivial)
      (declareRef := by intro σ σ' τ x p a hplace href; trivial)
      (seqNormal := by intro σ σ₁ σ₂ s t ctrl hstepS hstepT ihS ihT; trivial)
      (seqBreak := by intro σ σ₁ s t hstepS ihS; trivial)
      (seqContinue := by intro σ σ₁ s t hstepS ihS; trivial)
      (seqReturn := by intro σ σ₁ s t rv hstepS ihS; trivial)
      (iteTrue := by intro σ σ' c s t ctrl hcond hstepS ihS; trivial)
      (iteFalse := by intro σ σ' c s t ctrl hcond hstepT ihT; trivial)
      (whileFalse := by intro σ c body hcond; trivial)
      (whileTrueNormal := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal => trivial
        | breakResult => trivial
        | continueResult => trivial
        | returnResult rv => exact ihTail)
      (whileTrueBreak := by intro σ σ₁ c body hcond hbody ihBody; trivial)
      (whileTrueContinue := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal => trivial
        | breakResult => trivial
        | continueResult => trivial
        | returnResult rv => exact ihTail)
      (whileTrueReturn := by
        intro σ σ₁ c body rv hcond hbody ihBody
        intro hstable
        exact replay_stable_primitive_stmt_no_return hstable hbody)
      (block := by intro σ σ₁ σ₂ σ₃ ss ctrl hopen hblk hclose ihBlk; trivial)
      (breakStmt := by intro σ; trivial)
      (continueStmt := by intro σ; trivial)
      (returnNoneStmt := by intro σ; trivial)
      (returnSome := by intro σ e v hval; trivial)
      (nil := by intro σ; trivial)
      (consNormal := by intro σ σ₁ σ₂ s ss ctrl hstepS hstepSs ihS ihSs; trivial)
      (consBreak := by intro σ σ₁ s ss hstepS ihS; trivial)
      (consContinue := by intro σ σ₁ s ss hstepS ihS; trivial)
      (consReturn := by intro σ σ₁ s ss rv hstepS ihS; trivial)
      hstep

/-- replay-stable primitive body の while は raw return を起こさない。 -/
theorem replay_stable_primitive_body_while_no_return
    {σ σ' : State} {c : ValExpr} {body : CppStmt} {rv : Option Value} :
    ReplayStablePrimitiveStmt body →
    ¬ BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ' := by
  intro hstable hstep
  have hclaim := replay_stable_while_return_claim hstep
  exact hclaim hstable


theorem replay_stable_primitive_stmt_is_primitive_shape
    {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    (match st with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => False
     | .declareRef _ _ _ => False
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) := by
  intro h
  cases st <;> simp [ReplayStablePrimitiveStmt] at h ⊢

/-
For replay-stable primitive body + replay-stable condition, a single body-normal step
reconstructs a full CI boundary for the tail while.

重要:
- `summary.normalOut` は static に `some ⟨Γ, htyWhile⟩` と固定する。
- `summary.returnOut` は `none` でよい。replay-stable primitive body の while は
  raw return を起こさないからである。
-/

theorem replay_stable_primitive_stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hstable hty hσ hready hstep
  cases st <;> simp [ReplayStablePrimitiveStmt] at hstable
  case skip =>
    exact skip_stmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep
  case exprStmt e =>
    exact exprStmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep
  case assign p e =>
    exact assign_stmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep

/-! ## replay-stable primitive loop-body local support -/

/--
Replay-stable primitive bodies have a theorem-backed 4-channel loop-body
adequacy for any loop-body profile that already carries the required closed
normal/break/continue witnesses.

The non-normal channels are impossible for replay-stable primitive bodies, so
those obligations are discharged by contradiction.
-/
def replay_stable_primitive_loop_body_adequacy
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (P : LoopBodyControlProfile Γ body) :
    LoopBodyAdequacyCI Γ σ body P := by
  refine
    { normalSound := ?_
      breakSound := ?_
      continueSound := ?_
      returnSound := ?_ }
  · intro σ' hstep
    rcases P.normalClosed with ⟨hN, hNout⟩
    exact ⟨⟨Γ, hN⟩, hNout⟩
  · intro σ' hstep
    exfalso
    exact replay_stable_primitive_stmt_no_break hstable hstep
  · intro σ' hstep
    exfalso
    exact replay_stable_primitive_stmt_no_continue hstable hstep
  · intro rv σ' hstep
    exfalso
    exact replay_stable_primitive_stmt_no_return hstable hstep

private theorem replay_stable_primitive_stmt_normal_preserves_state_from_ready
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hstable hσ hready hstep
  cases st <;> simp [ReplayStablePrimitiveStmt] at hstable
  case skip =>
    cases hstep
    exact hσ
  case exprStmt e =>
    cases hstep
    exact hσ
  case assign p e =>
    cases hready with
    | assign hp hpready hv hvr =>
        exact
          assign_stmt_normal_preserves_scoped_typed_state_concrete
            (HasTypeStmtCI.assign hp hv)
            hσ
            (StmtReadyConcrete.assign hp hpready hv hvr)
            hstep


def replay_stable_primitive_loopBodyBoundary_after_normal
    {Γ : TypeEnv} {σ σ' : State} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    LoopBodyBoundaryCI Γ σ' body := by
  let hσ' : ScopedTypedStateConcrete Γ σ' :=
    replay_stable_primitive_stmt_normal_preserves_state_from_ready
      hstable
      hbody.dynamic.state
      hbody.dynamic.safe
      hstep

  let hsafe' : StmtReadyConcrete Γ σ' body :=
    replay_stable_primitive_stmt_ready_replay_concrete
      hstable
      hσ'
      hbody.dynamic.safe
      hstep

  exact
    { structural := hbody.structural
      profile := hbody.profile
      dynamic :=
        { state := hσ'
          safe := hsafe' }
      adequacy :=
        { normalSound := by
            intro σ2 hnormal
            rcases hbody.profile.normalClosed with ⟨hN, hNout⟩
            exact ⟨⟨Γ, hN⟩, hNout⟩
          breakSound := by
            intro σ2 hbreak
            exfalso
            exact replay_stable_primitive_stmt_no_break hstable hbreak
          continueSound := by
            intro σ2 hcontinue
            exfalso
            exact replay_stable_primitive_stmt_no_continue hstable hcontinue
          returnSound := by
            intro rv σ2 hreturn
            exfalso
            exact replay_stable_primitive_stmt_no_return hstable hreturn } }

/--
Replay-stable primitive bodies provide the delimiter reentry kernel expected by
`WhileBodyReentrySupportCI`.
-/
def replay_stable_primitive_loopReentryKernelCI
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hcstable : ReplayStableCondExpr c)
    (hc : HasValueType Γ c (.base .bool)) :
    LoopReentryKernelCI Γ c body :=
  { hc := hc
    cond_after_normal := by
      intro σ σ' hcond hbody hstep
      let hbody' : LoopBodyBoundaryCI Γ σ' body :=
        replay_stable_primitive_loopBodyBoundary_after_normal
          hstable hbody hstep
      exact
        replay_stable_cond_expr_ready_after_replay_stable_primitive
          hstable hcstable hbody'.dynamic.state hcond hstep
    cond_after_continue := by
      intro σ σ' hcond hbody hstep
      exfalso
      exact replay_stable_primitive_stmt_no_continue hstable hstep
    body_after_normal := by
      intro σ σ' hbody hstep
      exact replay_stable_primitive_loopBodyBoundary_after_normal
        hstable hbody hstep
    body_after_continue := by
      intro σ σ' hbody hstep
      exfalso
      exact replay_stable_primitive_stmt_no_continue hstable hstep }

/--
Witness-producing tail adequacy provider for a while statement.

This is the provider-facing analogue of `WhileTailAdequacyProviderCI`.  It is
kept in this replay-stable facts layer for now so the existing while kernel and
class interfaces remain source-compatible during the migration.
-/
structure WhileTailAdequacyWitnessProviderCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (static : BodyStaticBoundaryCI Γ (.whileStmt c body)) : Type where
  afterNormal :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .normal σ1 →
      BodyAdequacyWitnessCI Γ σ1 (.whileStmt c body) static.profile
  afterContinue :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .continueResult σ1 →
      BodyAdequacyWitnessCI Γ σ1 (.whileStmt c body) static.profile

namespace WhileTailAdequacyWitnessProviderCI

/-- Forget a witness-producing tail adequacy provider to the existing proof-only API. -/
def toWhileTailAdequacyProviderCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {static : BodyStaticBoundaryCI Γ (.whileStmt c body)}
    (P : WhileTailAdequacyWitnessProviderCI (σ := σ) (c := c) (body := body) static) :
    WhileTailAdequacyProviderCI Γ σ c body static :=
  { afterNormal := by
      intro σ1 hcond hstep
      exact (P.afterNormal hcond hstep).toBodyAdequacy
    afterContinue := by
      intro σ1 hcond hstep
      exact (P.afterContinue hcond hstep).toBodyAdequacy }

end WhileTailAdequacyWitnessProviderCI

/--
Witness-producing post-state adequacy after a replay-stable primitive body-normal
step.  The witness is obtained by transporting the original top-level while
adequacy along the concrete `whileTrueNormal` execution route.
-/
noncomputable def while_tail_adequacy_witness_after_body_normal
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hready : BodyReadyCI Γ σ (.whileStmt c body))
    (hcond : BigStepValue σ c (.bool true))
    (hbodyStep : BigStepStmt σ body .normal σ') :
    BodyAdequacyWitnessCI Γ σ' (.whileStmt c body) hready.static.profile :=
  { normalWitness := by
      intro σ2 htail
      exact
        (BodyAdequacyWitnessCI.ofBodyAdequacy hready.adequacy).normalWitness
          (BigStepStmt.whileTrueNormal hcond hbodyStep htail)
    returnWitness := by
      intro rv σ2 htail
      exact
        (BodyAdequacyWitnessCI.ofBodyAdequacy hready.adequacy).returnWitness
          (BigStepStmt.whileTrueNormal hcond hbodyStep htail) }

/--
Witness-producing post-state adequacy after a replay-stable primitive
body-continue step.  This is the continue-channel analogue of
`while_tail_adequacy_witness_after_body_normal`.
-/
noncomputable def while_tail_adequacy_witness_after_body_continue
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hready : BodyReadyCI Γ σ (.whileStmt c body))
    (hcond : BigStepValue σ c (.bool true))
    (hbodyStep : BigStepStmt σ body .continueResult σ') :
    BodyAdequacyWitnessCI Γ σ' (.whileStmt c body) hready.static.profile :=
  { normalWitness := by
      intro σ2 htail
      exact
        (BodyAdequacyWitnessCI.ofBodyAdequacy hready.adequacy).normalWitness
          (BigStepStmt.whileTrueContinue hcond hbodyStep htail)
    returnWitness := by
      intro rv σ2 htail
      exact
        (BodyAdequacyWitnessCI.ofBodyAdequacy hready.adequacy).returnWitness
          (BigStepStmt.whileTrueContinue hcond hbodyStep htail) }

def while_tail_adequacy_after_body_normal
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hready : BodyReadyCI Γ σ (.whileStmt c body))
    (hcond : BigStepValue σ c (.bool true))
    (hbodyStep : BigStepStmt σ body .normal σ') :
    BodyAdequacyCI Γ σ' (.whileStmt c body) hready.static.profile := by
  refine
    { normalSound := ?_
      returnSound := ?_ }
  · intro σ2 htail
    exact hready.adequacy.normalSound
      (BigStepStmt.whileTrueNormal hcond hbodyStep htail)
  · intro rv σ2 htail
    exact hready.adequacy.returnSound
      (BigStepStmt.whileTrueNormal hcond hbodyStep htail)

def while_tail_adequacy_after_body_continue
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hready : BodyReadyCI Γ σ (.whileStmt c body))
    (hcond : BigStepValue σ c (.bool true))
    (hbodyStep : BigStepStmt σ body .continueResult σ') :
    BodyAdequacyCI Γ σ' (.whileStmt c body) hready.static.profile := by
  refine
    { normalSound := ?_
      returnSound := ?_ }
  · intro σ2 htail
    exact hready.adequacy.normalSound
      (BigStepStmt.whileTrueContinue hcond hbodyStep htail)
  · intro rv σ2 htail
    exact hready.adequacy.returnSound
      (BigStepStmt.whileTrueContinue hcond hbodyStep htail)

/--
Post-state top-level while adequacy witness provider for replay-stable primitive
bodies.

This is the witness-producing companion of
`replay_stable_primitive_whileTailAdequacyProviderCI`.
-/
noncomputable def replay_stable_primitive_whileTailAdequacyWitnessProviderCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    @WhileTailAdequacyWitnessProviderCI Γ σ c body hentry.static := -- @を使ってσを明示 :=
  { afterNormal := by
      intro σ1 hcond hstep
      exact while_tail_adequacy_witness_after_body_normal
        hentry.toBodyReadyCI hcond hstep
    afterContinue := by
      intro σ1 hcond hstep
      exact while_tail_adequacy_witness_after_body_continue
        hentry.toBodyReadyCI hcond hstep }

/--
Post-state top-level while adequacy provider for replay-stable primitive bodies.

This is the remaining adequacy half of tail-boundary reconstruction.  The
dynamic half is supplied by `replay_stable_primitive_loopReentryKernelCI`.
-/
def replay_stable_primitive_whileTailAdequacyProviderCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailAdequacyProviderCI Γ σ c body hentry.static :=
  { afterNormal := by
      intro σ1 hcond hstep
      exact while_tail_adequacy_after_body_normal
        hentry.toBodyReadyCI hcond hstep
    afterContinue := by
      intro σ1 hcond hstep
      exact while_tail_adequacy_after_body_continue
        hentry.toBodyReadyCI hcond hstep }

/--
Replay-stable primitive body/condition gives the preferred reentry-support
package.  This is the concrete class route that avoids direct dependence on the
legacy `whileTailBoundaryKitCI_of_bodyClosureBoundaryCI` shell.
-/
def replay_stable_primitive_whileBodyReentrySupportCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hcstable : ReplayStableCondExpr c)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body) :
    WhileBodyReentrySupportCI hentry := by
  let hcurrent : WhileEntryBoundaryCI Γ σ c body :=
    whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry
  exact
    whileBodyReentrySupportCI_of_bodyClosureBoundaryCI
      hentry
      hloop
      (replay_stable_primitive_loopReentryKernelCI
        hstable hcstable hcurrent.hc)
      (replay_stable_primitive_whileTailAdequacyProviderCI hentry)


def bodyReadyCI_while_after_body_normal_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    BodyReadyCI Γ σ (.whileStmt c body) →
    BigStepValue σ c (.bool true) →
    BigStepStmt σ body .normal σ' →
    BodyReadyCI Γ σ' (.whileStmt c body) := by
  intro hstable hcstable htyWhile hready hcond hbodyStep

  rcases while_typing_data htyWhile with ⟨_, _, hN, _, _⟩

  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hready.dynamic.safe

  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    replay_stable_primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hstable hN hready.dynamic.state hreadyBody hbodyStep

  have hreadyWhile' : StmtReadyConcrete Γ σ' (.whileStmt c body) :=
    while_ready_after_body_normal_of_replay_stable_primitive
      hstable hcstable htyWhile hσ' hready.dynamic.safe hbodyStep

  have hadeq : BodyAdequacyCI Γ σ' (.whileStmt c body) hready.static.profile :=
    while_tail_adequacy_after_body_normal
       hready hcond hbodyStep

  exact
    { structural := hready.structural
      static := hready.static
      dynamic :=
        { state := hσ'
          safe := hreadyWhile' }
      adequacy := hadeq }

/-- wrapper for theorem-backed replay-stable primitive while tail boundary. -/
def bodyClosureBoundaryCI_while_after_body_normal_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    BigStepValue σ c (.bool true) →
    BigStepStmt σ body .normal σ' →
    BodyClosureBoundaryCI Γ σ' (.whileStmt c body) := by
  intro hstable hcstable htyWhile hready hcond hbodyStep
  exact
    (bodyReadyCI_while_after_body_normal_of_replay_stable_primitive
      hstable hcstable htyWhile hready.toBodyReadyCI hcond hbodyStep).toClosureBoundary

/--
Replay-stable primitive body / cond から構成される tail-boundary reconstruction kit。

Compatibility wrapper with the historical signature.  New proofs should prefer
`whileTailBoundaryKitCI_of_replay_stable_primitive_reentrySupport`, which factors
the same reconstruction through `LoopReentryKernelCI` plus
`WhileTailAdequacyProviderCI`.
-/
def whileTailBoundaryKitCI_of_replay_stable_primitive
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hcstable : ReplayStableCondExpr c)
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailBoundaryKitCI Γ σ c body := by
  refine
    { afterNormal := ?_
      afterContinue := ?_ }
  · intro σ1 hcond hstep
    exact
      bodyClosureBoundaryCI_while_after_body_normal_of_replay_stable_primitive
        hstable hcstable htyWhile hentry hcond hstep
  · intro σ1 _hcond hstep
    exfalso
    exact replay_stable_primitive_stmt_no_continue hstable hstep

/--
Replay-stable primitive tail-boundary reconstruction through the preferred
reentry-support route.
-/
def whileTailBoundaryKitCI_of_replay_stable_primitive_reentrySupport
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hcstable : ReplayStableCondExpr c)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body) :
    WhileTailBoundaryKitCI Γ σ c body :=
  (replay_stable_primitive_whileBodyReentrySupportCI
    hstable hcstable hentry hloop).toComponents.tailBoundary

/-- Replay-stable primitive body/cond yields a while-body class through the new
reentry-support route. -/
noncomputable def replay_stable_primitive_whileBodyClassCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hcstable : ReplayStableCondExpr c)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body) :
    WhileBodyClassCI Γ σ c body :=
  (replay_stable_primitive_whileBodyReentrySupportCI
    hstable hcstable hentry hloop).toClass

/--
Replay-stable primitive special case routed through the reentry-support while
surface.
-/
theorem while_function_body_closure_boundary_ci_of_replay_stable_primitive_reentrySupport
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    LoopBodyBoundaryCI Γ σ body →
    (∀ {σ1 : State},
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
      (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
        BigStepStmtDiv σ1 (.whileStmt c body)) →
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  intro hstable hcstable hentry hloop htailClosure
  exact
    while_function_body_closure_boundary_ci_of_reentrySupport
      hentry
      (replay_stable_primitive_whileBodyReentrySupportCI
        hstable hcstable hentry hloop)
      htailClosure

/--
Replay-stable primitive special case routed through the class-based while surface.
-/
theorem while_function_body_closure_boundary_ci_of_replay_stable_primitive_class
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    LoopBodyBoundaryCI Γ σ body →
    (∀ {σ1 : State},
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
      (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
        BigStepStmtDiv σ1 (.whileStmt c body)) →
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  intro hstable hcstable _htyWhile hentry hloop htailClosure
  exact
    while_function_body_closure_boundary_ci_of_replay_stable_primitive_reentrySupport
      hstable hcstable hentry hloop htailClosure

/--
Older replay-stable primitive theorem, now factored through the reentry-support
surface.
-/
theorem while_function_body_closure_boundary_ci_of_replay_stable_primitive
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    LoopBodyBoundaryCI Γ σ body →
    ((∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body) →
    (∀ {σ1 : State},
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
      (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
        BigStepStmtDiv σ1 (.whileStmt c body)) →
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  intro hstable hcstable htyWhile hentry hloop _hbodyClosure htailClosure
  exact
    while_function_body_closure_boundary_ci_of_replay_stable_primitive_class
      hstable hcstable htyWhile hentry hloop htailClosure

/--
BodyReadyCI entry surface から honest while kernel へ降ろす互換 wrapper。
-/
theorem while_function_body_closure_ci_of_replay_stable_primitive_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    BodyReadyCI Γ σ (.whileStmt c body) →
    LoopBodyBoundaryCI Γ σ body →
    ((∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body) →
    (∀ {σ1 : State},
      BodyReadyCI Γ σ1 (.whileStmt c body) →
      (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
        BigStepStmtDiv σ1 (.whileStmt c body)) →
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  intro hstable hcstable htyWhile hentry hloop hbodyClosure htailClosure
  exact
    while_function_body_closure_boundary_ci_of_replay_stable_primitive
      hstable hcstable htyWhile hentry.toClosureBoundary hloop hbodyClosure
      (fun {σ1} htailBoundary =>
        htailClosure (σ1 := σ1) htailBoundary.toBodyReadyCI)

end Cpp
