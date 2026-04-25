import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyPrimitiveClosureCI
import CppFormalization.Cpp2.Closure.Internal.WhileBodyClassCI
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReplayStablePrimitiveFacts
import CppFormalization.Cpp2.Boundary.FunctionBody

namespace Cpp

/-!
# Closure.Internal.FunctionBodyReplayStablePrimitiveWhileFacts

Replay-stable primitive `while` bodies give a theorem-backed tail-boundary
reconstruction for function-body closure.

This file isolates the replay-stable primitive `while` special case from
`FunctionBodyClosureCI.lean`, so the latter can shrink toward the canonical
global entry theorems.
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
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
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
`continue` branch は primitive replay-stable body では矛盾で閉じる。
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

/-- Replay-stable primitive body/cond yields a while-body class. -/
noncomputable def replay_stable_primitive_whileBodyClassCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hcstable : ReplayStableCondExpr c)
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body) :
    WhileBodyClassCI Γ σ c body :=
  { loopBoundary := hloop
    tailBoundary :=
      whileTailBoundaryKitCI_of_replay_stable_primitive
        hstable hcstable htyWhile hentry }

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
  intro hstable hcstable htyWhile hentry hloop htailClosure
  exact
    while_function_body_closure_boundary_ci_of_class
      htyWhile
      hentry
      (replay_stable_primitive_whileBodyClassCI
        hstable hcstable htyWhile hentry hloop)
      htailClosure

/--
Older replay-stable primitive theorem, now factored through the class-based surface.
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
