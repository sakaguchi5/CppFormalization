import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureConcreteRefined
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Closure.Internal.WhileNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.CurrentShellCI
import CppFormalization.Cpp2.Closure.Internal.WhileFunctionClosureKernelCI
import CppFormalization.Cpp2.Boundary.FunctionBody

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureCI

CI-centric function-body closure layer.

目的:
- old `BodyReady` を主線から降格し、internal closure の driver を `BodyReadyCI` に移す。
- 既存 concrete kernel (`StmtControlPreservation`, `ReadinessBoundaryConcrete`,
  `InternalClosureRoadmapConcrete`) はそのまま利用する。
- まだ theorem-backed でない function-body case split は、ここでは honest な
  CI-boundary obligation として切り出す。
- ただし while については、replay-stable primitive body + replay-stable cond の
  部分では theorem-backed な tail-boundary reconstruction を接続し、
  CI case-driver 側の open surface を狭める。

注:
- `BigStepStmt` は mutual inductive なので、while-return の否定は
  `termination_by` つきの直接再帰ではなく、導出 recursor に motive を与える形で処理する。
  これは `StmtControlPreservation.lean` の bundle+recursor の軽量版である。
-/

/-- Forget the CI-sensitive fields and recover the existing refined concrete boundary. -/
theorem bodyReadyConcrete_of_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    BodyReadyCI Γ σ st → BodyReadyConcrete Γ σ st := by
  intro h
  exact {
    wf := h.wf
    typed := h.typed0
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped
    state := h.state
    safe := h.safe
  }

/-- forgetful map from the new assembled boundary to the refined concrete boundary. -/
theorem bodyReadyConcrete_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    BodyClosureBoundaryCI Γ σ st → BodyReadyConcrete Γ σ st := by
  intro h
  exact bodyReadyConcrete_of_bodyReadyCI h.toBodyReadyCI

/-- Primitive case already follows from the refined concrete layer once we forget CI extras. -/
theorem primitive_stmt_function_body_step_or_diverges_ci
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmtConcrete st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hprim hready
  exact
    primitive_stmt_function_body_step_or_diverges_concrete_refined
      hprim (bodyReadyConcrete_of_bodyReadyCI hready)

/-- entry version of the primitive case. -/
theorem primitive_stmt_function_body_step_or_diverges_body_closure
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmtConcrete st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hprim hready
  exact
    primitive_stmt_function_body_step_or_diverges_concrete_refined
      hprim (bodyReadyConcrete_of_bodyClosureBoundaryCI hready)

/-
Dead candidate moved out of the live CI surface.

axiom seq_function_body_closure_ci
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    BodyReadyCI Γ σ (.seq s t) →
    (∀ {σ'},
      BigStepStmt σ s .normal σ' →
      BodyReadyCI Γ σ' t →
      (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨ BigStepStmtDiv σ' t) →
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨ BigStepStmtDiv σ (.seq s t)

axiom ite_function_body_closure_ci
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    BodyReadyCI Γ σ (.ite c s t) →
    (BodyReadyCI Γ σ s →
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s) →
    (BodyReadyCI Γ σ t →
      (∃ ex σ', BigStepFunctionBody σ t ex σ') ∨ BigStepStmtDiv σ t) →
    (∃ ex σ', BigStepFunctionBody σ (.ite c s t) ex σ') ∨
      BigStepStmtDiv σ (.ite c s t)

axiom block_function_body_closure_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyReadyCI Γ σ (.block ss) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss)
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
      (skip := by
        intro σ
        trivial)
      (expr := by
        intro σ e v hval
        trivial)
      (assign := by
        intro σ σ' p e v hval hassign
        trivial)
      (declareObjNone := by
        intro σ σ' τ x hdecl
        trivial)
      (declareObjSome := by
        intro σ σ' τ x e v hval hdecl
        trivial)
      (declareRef := by
        intro σ σ' τ x p a hplace href
        trivial)
      (seqNormal := by
        intro σ σ₁ σ₂ s t ctrl hstepS hstepT ihS ihT
        trivial)
      (seqBreak := by
        intro σ σ₁ s t hstepS ihS
        trivial)
      (seqContinue := by
        intro σ σ₁ s t hstepS ihS
        trivial)
      (seqReturn := by
        intro σ σ₁ s t rv hstepS ihS
        trivial)
      (iteTrue := by
        intro σ σ' c s t ctrl hcond hstepS ihS
        trivial)
      (iteFalse := by
        intro σ σ' c s t ctrl hcond hstepT ihT
        trivial)
      (whileFalse := by
        intro σ c body hcond
        trivial)
      (whileTrueNormal := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal =>
            trivial
        | breakResult =>
            trivial
        | continueResult =>
            trivial
        | returnResult rv =>
            exact ihTail)
      (whileTrueBreak := by
        intro σ σ₁ c body hcond hbody ihBody
        trivial)
      (whileTrueContinue := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal =>
            trivial
        | breakResult =>
            trivial
        | continueResult =>
            trivial
        | returnResult rv =>
            exact ihTail)
      (whileTrueReturn := by
        intro σ σ₁ c body rv hcond hbody ihBody
        intro hstable
        exact replay_stable_primitive_stmt_no_return hstable hbody)
      (block := by
        intro σ σ₁ σ₂ σ₃ ss ctrl hopen hblk hclose ihBlk
        trivial)
      (breakStmt := by
        intro σ
        trivial)
      (continueStmt := by
        intro σ
        trivial)
      (returnNoneStmt := by
        intro σ
        trivial)
      (returnSome := by
        intro σ e v hval
        trivial)
      (nil := by
        intro σ
        trivial)
      (consNormal := by
        intro σ σ₁ σ₂ s ss ctrl hstepS hstepSs ihS ihSs
        trivial)
      (consBreak := by
        intro σ σ₁ s ss hstepS ihS
        trivial)
      (consContinue := by
        intro σ σ₁ s ss hstepS ihS
        trivial)
      (consReturn := by
        intro σ σ₁ s ss rv hstepS ihS
        trivial)
      hstep

/-- replay-stable primitive body の while は raw return を起こさない。 -/
theorem replay_stable_primitive_body_while_no_return
    {σ σ' : State} {c : ValExpr} {body : CppStmt} {rv : Option Value} :
    ReplayStablePrimitiveStmt body →
    ¬ BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ' := by
  intro hstable hstep
  have hclaim := replay_stable_while_return_claim hstep
  exact hclaim hstable

/-
For replay-stable primitive body + replay-stable condition, a single body-normal step
reconstructs a full CI boundary for the tail while.

重要:
- `summary.normalOut` は static に `some ⟨Γ, htyWhile⟩` と固定する。
- `summary.returnOut` は `none` でよい。replay-stable primitive body の while は
  raw return を起こさないからである。
-/
def bodyReadyCI_while_after_body_normal_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    BodyReadyCI Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    BodyReadyCI Γ σ' (.whileStmt c body) := by
  intro hstable hcstable htyWhile hready hbodyStep
  rcases while_typing_data htyWhile with ⟨_, _, hN, _, _⟩
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hready.safe
  have hprim : PrimitiveNormalStmt body :=
    replay_stable_primitive_stmt_is_primitive_normal hstable
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim hN hready.state hreadyBody hbodyStep
  have hsafe' : StmtReadyConcrete Γ σ' (.whileStmt c body) :=
    while_ready_after_body_normal_of_replay_stable_primitive
      hstable hcstable htyWhile hσ' hready.safe hbodyStep
  refine {
    wf := hready.wf
    typed0 := hready.typed0
    breakScoped := hready.breakScoped
    continueScoped := hready.continueScoped
    state := hσ'
    safe := hsafe'
    summary := {
      normalOut := some ⟨Γ, htyWhile⟩
      returnOut := none
    }
    normalSound := ?_
    returnSound := ?_
  }
  · intro σ'' hstepNorm
    exact ⟨⟨Γ, htyWhile⟩, rfl⟩
  · intro rv σ'' hstepRet
    have hfalse : False :=
      replay_stable_primitive_body_while_no_return hstable hstepRet
    exact False.elim hfalse

/-- wrapper for theorem-backed replay-stable primitive while tail boundary. -/
def bodyClosureBoundaryCI_while_after_body_normal_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    BodyClosureBoundaryCI Γ σ' (.whileStmt c body) := by
  intro hstable hcstable htyWhile hready hbodyStep
  exact
    (bodyReadyCI_while_after_body_normal_of_replay_stable_primitive
      hstable hcstable htyWhile hready.toBodyReadyCI hbodyStep).toClosureBoundary

/--
Replay-stable primitive body / cond から構成される tail-boundary reconstruction kit.
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
  · intro σ1 hstep
    exact
      bodyClosureBoundaryCI_while_after_body_normal_of_replay_stable_primitive
        hstable hcstable htyWhile hentry hstep
  · intro σ1 hstep
    exfalso
    exact replay_stable_primitive_stmt_no_continue hstable hstep

/--
Replay-stable primitive special case routed through the honest while kernel surface.

重要:
- ここではもう generic `while_function_body_closure_ci` shell を使わない。
- 代わりに、loop-body local closure と tail-boundary reconstruction を
  明示前提にした honest kernel theorem へ落とす。
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
  intro hstable hcstable htyWhile hentry hloop hbodyClosure htailClosure
  exact
    while_function_body_closure_boundary_ci_honest
      htyWhile
      hentry
      hloop
      hbodyClosure
      (whileTailBoundaryKitCI_of_replay_stable_primitive
        hstable hcstable htyWhile hentry)
      htailClosure

/--
BodyReadyCI entry surface から honest while kernel へ降ろす互換 wrapper.

この theorem は旧 `while_function_body_closure_ci_of_replay_stable_primitive` と違い、
loop-body boundary と local body closure を明示前提に持つ。
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

/-
Current live CI shell axioms were moved to `CurrentShellCI.lean`.

axiom body_ready_ci_function_body_progress_or_diverges_by_cases ...

axiom body_closure_ci_function_body_progress_or_diverges_by_cases ...
-/

/-- CI-boundary master theorem target. -/
theorem body_ready_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  exact body_ready_ci_function_body_progress_or_diverges_by_cases hfrag hready

/-- canonical entry theorem for function-body closure. -/
theorem body_closure_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  exact body_closure_ci_function_body_progress_or_diverges_by_cases hfrag hready

end Cpp
