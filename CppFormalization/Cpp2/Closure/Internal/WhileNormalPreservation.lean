import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel

namespace Cpp

/-!
`while` の normal-path preservation。

ここで直接示したいのは
`BigStepStmt σ (.whileStmt c body) .normal σ'`
なら `ScopedTypedStateConcrete Γ σ'`
が保たれることだが、その本体は

1. 条件が false で即 normal 終了する場合
2. body が normal で 1 周進んでから tail loop が normal 終了する場合
3. body が break でその場で normal 終了する場合
4. body が continue で 1 周進んでから tail loop が normal 終了する場合

の 4 分岐である。

このファイルでは generic な while 分解を与えたうえで、
step 4/5 として
- `while_ready_after_body_*` の theorem-backed な再構成層を追加し
- replay-stable primitive body について、break 込み while preservation を
  generic axiom に頼らず再構成する

ところまで進める。

condition replay kernel 導入後は、replay-stable primitive body 版については
post-state の condition readiness を外から受け取る必要はない。
`ReplayStableCondExpr c` と initial while-ready から内部で再構成する。
-/

/- =========================================================
   1. typing / readiness / operational 分解
   ========================================================= -/

theorem while_typing_data
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    Δ = Γ ∧
    HasValueType Γ c (.base .bool) ∧
    HasTypeStmtCI .normalK Γ body Γ ∧
    HasTypeStmtCI .breakK Γ body Γ ∧
    HasTypeStmtCI .continueK Γ body Γ := by
  intro h
  exact while_normal_typing_data h

theorem while_ready_body_data
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    StmtReadyConcrete Γ σ body := by
  intro h
  cases h with
  | whileStmt _ _ hbody =>
      simpa using hbody

theorem while_ready_cond_data
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    HasValueType Γ c (.base .bool) ∧ ExprReadyConcrete Γ σ c (.base .bool) := by
  intro h
  cases h with
  | whileStmt hc hcr _ =>
      exact ⟨hc, hcr⟩

/--
Full generic な residual-readiness reconstruction はまだ kernel axiom のまま残す。
理由は condition 側の replay theorem が full generic にはまだ無いからである。
-/
axiom while_ready_after_body_normal
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ body Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body)

axiom while_ready_after_body_continue
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ body Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body)

/--
Step 4 の theorem 化の中核。
condition と body の post-state replay witness が外から与えられれば、
whole-while ready は constructor で再構成できる。
-/
theorem while_ready_after_body_normal_from_replay
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ExprReadyConcrete Γ σ' c (.base .bool) →
    StmtReadyConcrete Γ σ' body →
    BigStepStmt σ body .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro htyWhile hcondReady hbodyReady _
  rcases while_typing_data htyWhile with ⟨_, hc, _, _, _⟩
  exact StmtReadyConcrete.whileStmt hc hcondReady hbodyReady

/--
continue 分岐も同様。
本質は step result ではなく、post-state での condition/body replay witness である。
-/
theorem while_ready_after_body_continue_from_replay
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ExprReadyConcrete Γ σ' c (.base .bool) →
    StmtReadyConcrete Γ σ' body →
    BigStepStmt σ body .continueResult σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro htyWhile hcondReady hbodyReady _
  rcases while_typing_data htyWhile with ⟨_, hc, _, _, _⟩
  exact StmtReadyConcrete.whileStmt hc hcondReady hbodyReady

theorem while_normal_data
    {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    BigStepStmt σ (.whileStmt c body) .normal σ' →
      (σ' = σ) ∨
      (∃ σ1,
        BigStepStmt σ body .normal σ1 ∧
        BigStepStmt σ1 (.whileStmt c body) .normal σ') ∨
      (∃ σ1,
        BigStepStmt σ body .breakResult σ1 ∧
        σ' = σ1) ∨
      (∃ σ1,
        BigStepStmt σ body .continueResult σ1 ∧
        BigStepStmt σ1 (.whileStmt c body) .normal σ') := by
  intro h
  cases h with
  | whileFalse _ =>
      exact Or.inl rfl
  | whileTrueNormal _ hBody hTail =>
      exact Or.inr (Or.inl ⟨_, hBody, hTail⟩)
  | whileTrueBreak _ hBody =>
      exact Or.inr (Or.inr (Or.inl ⟨_, hBody, rfl⟩))
  | whileTrueContinue _ hBody hTail =>
      exact Or.inr (Or.inr (Or.inr ⟨_, hBody, hTail⟩))


/- =========================================================
   2. generic theorem from body/tail subproofs
   ========================================================= -/


def WhileTailClosed
    (Γ : TypeEnv) (σ' : State) (c : ValExpr) (body : CppStmt) : Prop :=
  ∀ {σ1},
    ScopedTypedStateConcrete Γ σ1 →
    StmtReadyConcrete Γ σ1 (.whileStmt c body) →
    BigStepStmt σ1 (.whileStmt c body) .normal σ' →
    ScopedTypedStateConcrete Γ σ'


theorem while_normal_stop_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    σ' = σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hEq
  rcases while_typing_data hty with ⟨hΔ, _, _, _, _⟩
  subst hΔ
  subst hEq
  exact hσ


theorem while_normal_body_normal_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .normal σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    (∃ σ1,
      BigStepStmt σ body .normal σ1 ∧
      BigStepStmt σ1 (.whileStmt c body) .normal σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hbodyNorm htail hcase
  rcases while_typing_data hty with ⟨hΔ, _, hbodyTy, _, _⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, htailStep⟩
  have hreadyBody : StmtReadyConcrete Δ σ body :=
    while_ready_body_data hready
  have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
    hbodyNorm hreadyBody hbodyStep
  have hreadyTail : StmtReadyConcrete Δ σ1 (.whileStmt c body) :=
    while_ready_after_body_normal hbodyTy hσ1 hready hbodyStep
  exact htail hσ1 hreadyTail htailStep


theorem while_normal_body_break_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .breakResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    (∃ σ1,
      BigStepStmt σ body .breakResult σ1 ∧
      σ' = σ1) →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hbodyBreak hcase
  rcases while_typing_data hty with ⟨hΔ, _, _, _, _⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, hEq⟩
  have hreadyBody : StmtReadyConcrete Δ σ body :=
    while_ready_body_data hready
  have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
    hbodyBreak hreadyBody hbodyStep
  subst hEq
  exact hσ1


theorem while_normal_body_continue_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .continueResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    (∃ σ1,
      BigStepStmt σ body .continueResult σ1 ∧
      BigStepStmt σ1 (.whileStmt c body) .normal σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hbodyCont htail hcase
  rcases while_typing_data hty with ⟨hΔ, _, hbodyTy, _, _⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, htailStep⟩
  have hreadyBody : StmtReadyConcrete Δ σ body :=
    while_ready_body_data hready
  have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
    hbodyCont hreadyBody hbodyStep
  have hreadyTail : StmtReadyConcrete Δ σ1 (.whileStmt c body) :=
    while_ready_after_body_continue hbodyTy hσ1 hready hbodyStep
  exact htail hσ1 hreadyTail htailStep


theorem while_normal_preserves_scoped_typed_state_from_body_and_tail
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .normal σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .breakResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .continueResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep hbodyNorm hbodyBreak hbodyCont htail
  rcases while_normal_data hstep with hstop | hnorm | hbreak | hcont
  · exact while_normal_stop_case_preserves_scoped_typed_state
      hty hσ hstop
  · exact while_normal_body_normal_case_preserves_scoped_typed_state
      hty hσ hready hbodyNorm htail hnorm
  · exact while_normal_body_break_case_preserves_scoped_typed_state
      hty hσ hready hbodyBreak hbreak
  · exact while_normal_body_continue_case_preserves_scoped_typed_state
      hty hσ hready hbodyCont htail hcont


/- =========================================================
   3. primitive body の corollary
   ========================================================= -/

theorem primitive_normal_stmt_no_break
    {σ σ' : State} {st : CppStmt} :
    PrimitiveNormalStmt st →
    ¬ BigStepStmt σ st .breakResult σ' := by
  intro hprim hbreak
  cases st <;>
    simp [PrimitiveNormalStmt] at hprim <;>
    cases hbreak


theorem primitive_normal_stmt_no_continue
    {σ σ' : State} {st : CppStmt} :
    PrimitiveNormalStmt st →
    ¬ BigStepStmt σ st .continueResult σ' := by
  intro hprim hcont
  cases st <;>
    simp [PrimitiveNormalStmt] at hprim <;>
    cases hcont


theorem primitive_body_while_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    PrimitiveNormalStmt body →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    (∀ {σ1},
      ScopedTypedStateConcrete Γ σ1 →
      StmtReadyConcrete Γ σ1 (.whileStmt c body) →
      BigStepStmt σ1 (.whileStmt c body) .normal σ' →
      ScopedTypedStateConcrete Γ σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep htail
  rcases while_typing_data hty with ⟨_, _, hbodyTy, _, _⟩
  refine while_normal_preserves_scoped_typed_state_from_body_and_tail
    hty hσ hready hstep ?_ ?_ ?_ ?_
  · intro σ1 hreadyBody hbodyStep
    exact primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim hbodyTy hσ hreadyBody hbodyStep
  · intro σ1 hreadyBody hbodyStep
    exfalso
    exact primitive_normal_stmt_no_break hprim hbodyStep
  · intro σ1 hreadyBody hbodyStep
    exfalso
    exact primitive_normal_stmt_no_continue hprim hbodyStep
  · intro σ1 hσ1 hreadyTail htailStep
    exact htail hσ1 hreadyTail htailStep


theorem while_normal_preserves_scoped_typed_state_concrete_of_primitive_body
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    PrimitiveNormalStmt body →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep htail
  exact primitive_body_while_normal_preserves_scoped_typed_state_concrete
    hprim hty hσ hready hstep htail


/- =========================================================
   4. theorem-backed replay reconstruction for replay-stable primitive body
   ========================================================= -/

theorem replay_stable_primitive_stmt_is_primitive_normal
    {st : CppStmt} :
    ReplayStablePrimitiveStmt st → PrimitiveNormalStmt st := by
  intro h
  cases st <;> simp [ReplayStablePrimitiveStmt, PrimitiveNormalStmt] at h ⊢


theorem replay_stable_primitive_stmt_no_break
    {σ σ' : State} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    ¬ BigStepStmt σ st .breakResult σ' := by
  intro hstable hbreak
  cases st <;>
    simp [ReplayStablePrimitiveStmt] at hstable <;>
    cases hbreak


theorem replay_stable_primitive_stmt_no_continue
    {σ σ' : State} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    ¬ BigStepStmt σ st .continueResult σ' := by
  intro hstable hcont
  cases st <;>
    simp [ReplayStablePrimitiveStmt] at hstable <;>
    cases hcont

/--
Step 4 の theorem 化その1。
replay-stable primitive body では、body の normal 実行後
- body 自体の ready は primitive replay kernel で再構成できる
- condition ready は condition replay kernel で再構成できる

したがって post-state の while-ready は theorem で再構成できる。
-/
theorem while_ready_after_body_normal_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hstable hcstable htyWhile hσ' hreadyWhile hstepBody
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hreadyWhile
  have hreadyBody' : StmtReadyConcrete Γ σ' body :=
    replay_stable_primitive_stmt_ready_replay_concrete
      hstable hσ' hreadyBody hstepBody
  have hcondReady0 : ExprReadyConcrete Γ σ c (.base .bool) :=
    (while_ready_cond_data hreadyWhile).2
  have hcondReady' : ExprReadyConcrete Γ σ' c (.base .bool) :=
    replay_stable_cond_expr_ready_after_replay_stable_primitive
      hstable hcstable hσ' hcondReady0 hstepBody
  exact while_ready_after_body_normal_from_replay
    htyWhile hcondReady' hreadyBody' hstepBody

/--
continue 分岐も同様。
replay-stable primitive body には continue 実行そのものが存在しないので、
continue 分岐の residual-readiness は contradiction から閉じる。
-/
theorem while_ready_after_body_continue_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hstable _ _ _ _ hstepBody
  have hfalse : False := replay_stable_primitive_stmt_no_continue hstable hstepBody
  exact False.elim hfalse


/- =========================================================
   5. break 込みでの replay-stable primitive while preservation 再構成
   ========================================================= -/

/--
Step 5。
replay-stable primitive body の while-preservation を、generic residual-readiness axiom に頼らず
replay kernel と break/continue impossibility から組み直す。

condition replay kernel 導入後は、`ReplayStableCondExpr c` から body-normal 分岐の
condition ready も内部で再構成できるので、追加の replay hypothesis は不要である。
-/
theorem replay_stable_primitive_body_while_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hstable hcstable htyWhile hσ hready hstep htail
  rcases while_typing_data htyWhile with ⟨hΔ, _, hN, _, _⟩
  subst hΔ
  rcases while_normal_data hstep with hstop | hnorm | hbreak | hcont
  · subst hstop
    exact hσ
  · rcases hnorm with ⟨σ1, hbodyStep, htailStep⟩
    have hreadyBody : StmtReadyConcrete Δ σ body :=
      while_ready_body_data hready
    have hprim : PrimitiveNormalStmt body :=
      replay_stable_primitive_stmt_is_primitive_normal hstable
    have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
      primitive_stmt_normal_preserves_scoped_typed_state_concrete
        hprim hN hσ hreadyBody hbodyStep
    have hreadyTail : StmtReadyConcrete Δ σ1 (.whileStmt c body) :=
      while_ready_after_body_normal_of_replay_stable_primitive
        hstable hcstable htyWhile hσ1 hready hbodyStep
    exact htail hσ1 hreadyTail htailStep
  · rcases hbreak with ⟨σ1, hbodyStep, _⟩
    have hfalse : False := replay_stable_primitive_stmt_no_break hstable hbodyStep
    exact False.elim hfalse
  · rcases hcont with ⟨σ1, hbodyStep, _⟩
    have hfalse : False := replay_stable_primitive_stmt_no_continue hstable hbodyStep
    exact False.elim hfalse

end Cpp
