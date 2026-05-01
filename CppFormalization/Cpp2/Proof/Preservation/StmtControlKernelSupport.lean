import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.ReadinessInversions
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReentryReadyKernelCI
import CppFormalization.Cpp2.Closure.Internal.BlockNormalPreservation
import CppFormalization.Cpp2.Closure.Foundation.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Lemmas.ExprTypeUniqueness
import CppFormalization.Cpp2.Lemmas.TransitionDeterminism


namespace Cpp

/-!
# Proof.Preservation.StmtControlKernelSupport

`StmtControlKernel` / `StmtControlPreservationV2` で使う while / assign /
block-open-scope の補助層。
main recursor から support obligations を分離して、
compatibility recursion 本体を読みやすく保つ。
-/


/-- body branch IH から 1-step 後の concrete state を得るだけの補助。 -/
theorem whileBodyConcrete
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (ihBody :
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ body →
      ScopedTypedStateConcrete Γ σ')
    (hsc : ScopedTypedStateConcrete Γ σ)
    (hreadyWhile : StmtReadyConcrete Γ σ (.whileStmt c body)) :
    ScopedTypedStateConcrete Γ σ' := by
  exact ihBody hsc (while_ready_body_data hreadyWhile)

theorem whileTailReadyNormal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hsc : ScopedTypedStateConcrete Γ σ)
    (hreadyWhile : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hbody : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  let K := mkWhileReentry hc hN hB hC hsc hreadyWhile
  exact whileStmtReady_after_normal hc K hbody

theorem whileTailReadyContinue
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hsc : ScopedTypedStateConcrete Γ σ)
    (hreadyWhile : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hbody : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  let K := mkWhileReentry hc hN hB hC hsc hreadyWhile
  exact whileStmtReady_after_continue hc K hbody

theorem whileNormalNormalCase
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ0 σ1 σ2 : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hbody : BigStepStmt σ0 body .normal σ1)
    (ihBody :
      ScopedTypedStateConcrete Γ σ0 →
      StmtReadyConcrete Γ σ0 body →
      ScopedTypedStateConcrete Γ σ1)
    (ihTail :
      ScopedTypedStateConcrete Γ σ1 →
      StmtReadyConcrete Γ σ1 (.whileStmt c body) →
      ScopedTypedStateConcrete Γ σ2) :
    ScopedTypedStateConcrete Γ σ0 →
    StmtReadyConcrete Γ σ0 (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ2 := by
  intro hsc_in hreadyWhile
  have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
    whileBodyConcrete ihBody hsc_in hreadyWhile
  have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
    whileTailReadyNormal mkWhileReentry hc hN hB hC hsc_in hreadyWhile hbody
  exact ihTail hsc1 hreadyTail

theorem whileBreakCase
    {Γ : TypeEnv} {σ0 σ1 : State} {c : ValExpr} {body : CppStmt}
    (ihBody :
      ScopedTypedStateConcrete Γ σ0 →
      StmtReadyConcrete Γ σ0 body →
      ScopedTypedStateConcrete Γ σ1) :
    ScopedTypedStateConcrete Γ σ0 →
    StmtReadyConcrete Γ σ0 (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ1 := by
  intro hsc_in hreadyWhile
  exact whileBodyConcrete ihBody hsc_in hreadyWhile

theorem whileContinueNormalCase
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ0 σ1 σ2 : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hbody : BigStepStmt σ0 body .continueResult σ1)
    (ihBody :
      ScopedTypedStateConcrete Γ σ0 →
      StmtReadyConcrete Γ σ0 body →
      ScopedTypedStateConcrete Γ σ1)
    (ihTail :
      ScopedTypedStateConcrete Γ σ1 →
      StmtReadyConcrete Γ σ1 (.whileStmt c body) →
      ScopedTypedStateConcrete Γ σ2) :
    ScopedTypedStateConcrete Γ σ0 →
    StmtReadyConcrete Γ σ0 (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ2 := by
  intro hsc_in hreadyWhile
  have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
    whileBodyConcrete ihBody hsc_in hreadyWhile
  have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
    whileTailReadyContinue mkWhileReentry hc hN hB hC hsc_in hreadyWhile hbody
  exact ihTail hsc1 hreadyTail

theorem whileNormalReturnCase
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ Δ : TypeEnv} {σ0 σ1 σ2 : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hbody : BigStepStmt σ0 body .normal σ1)
    (ihBody :
      ScopedTypedStateConcrete Γ σ0 →
      StmtReadyConcrete Γ σ0 body →
      ScopedTypedStateConcrete Γ σ1)
    (ihTail :
      ScopedTypedStateConcrete Γ σ1 →
      StmtReadyConcrete Γ σ1 (.whileStmt c body) →
      ScopedTypedStateConcrete Δ σ2) :
    ScopedTypedStateConcrete Γ σ0 →
    StmtReadyConcrete Γ σ0 (.whileStmt c body) →
    ScopedTypedStateConcrete Δ σ2 := by
  intro hsc_in hreadyWhile
  have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
    whileBodyConcrete ihBody hsc_in hreadyWhile
  have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
    whileTailReadyNormal mkWhileReentry hc hN hB hC hsc_in hreadyWhile hbody
  exact ihTail hsc1 hreadyTail

theorem whileContinueReturnCase
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ Δ : TypeEnv} {σ0 σ1 σ2 : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hbody : BigStepStmt σ0 body .continueResult σ1)
    (ihBody :
      ScopedTypedStateConcrete Γ σ0 →
      StmtReadyConcrete Γ σ0 body →
      ScopedTypedStateConcrete Γ σ1)
    (ihTail :
      ScopedTypedStateConcrete Γ σ1 →
      StmtReadyConcrete Γ σ1 (.whileStmt c body) →
      ScopedTypedStateConcrete Δ σ2) :
    ScopedTypedStateConcrete Γ σ0 →
    StmtReadyConcrete Γ σ0 (.whileStmt c body) →
    ScopedTypedStateConcrete Δ σ2 := by
  intro hsc_in hreadyWhile
  have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
    whileBodyConcrete ihBody hsc_in hreadyWhile
  have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
    whileTailReadyContinue mkWhileReentry hc hN hB hC hsc_in hreadyWhile hbody
  exact ihTail hsc1 hreadyTail

theorem whileReturnLeafCase
    {Γ Δ : TypeEnv} {σ0 σ1 : State} {c : ValExpr} {body : CppStmt}
    (ihBody :
      ScopedTypedStateConcrete Γ σ0 →
      StmtReadyConcrete Γ σ0 body →
      ScopedTypedStateConcrete Δ σ1) :
    ScopedTypedStateConcrete Γ σ0 →
    StmtReadyConcrete Γ σ0 (.whileStmt c body) →
    ScopedTypedStateConcrete Δ σ1 := by
  intro hsc_in hreadyWhile
  exact ihBody hsc_in (while_ready_body_data hreadyWhile)

theorem blockStmtCase
    {k : ControlKind} {Γ Θ : TypeEnv} {ss : StmtBlock}
    {σ σ0 σ1 σ2 : State}
    {htyB : HasTypeBlockCI k (pushTypeScope Γ) ss Θ}
    {hopen : OpenScope σ σ0}
    {hclose : CloseScope σ1 σ2}
    (ihBlk :
      ScopedTypedStateConcrete (pushTypeScope Γ) σ0 →
      BlockReadyConcrete (pushTypeScope Γ) σ0 ss →
      ScopedTypedStateConcrete Θ σ1) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.block ss) →
    ScopedTypedStateConcrete Γ σ2 := by
  intro hsc_in hready_block
  have hsc_open : ScopedTypedStateConcrete (pushTypeScope Γ) σ0 :=
    openScope_preserves_scoped_typed_state_concrete hsc_in hopen
  have hreadyBody : BlockReadyConcrete (pushTypeScope Γ) σ0 ss :=
    block_ready_opened_body hready_block hopen
  have hsc_body : ScopedTypedStateConcrete Θ σ1 :=
    ihBlk hsc_open hreadyBody
  have hExt : TopFrameExtensionOf Γ Θ :=
    block_ci_topFrameExtension htyB
  exact closeScope_preserves_outer_from_topFrameExtension hExt hsc_body hclose

theorem assign_ready_data
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {e : ValExpr} :
    StmtReadyConcrete Γ σ (.assign p e) →
    ∃ τ, HasPlaceType Γ p τ ∧ PlaceReadyConcrete Γ σ p τ ∧
         HasValueType Γ e τ ∧ ExprReadyConcrete Γ σ e τ := by
  intro hready
  cases hready with
  | assign hp hrp hv hre =>
      exact ⟨_, hp, hrp, hv, hre⟩

theorem assign_preservation_inputs
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {e : ValExpr} {τ : CppType}
    (hp : HasPlaceType Γ p τ)
    (hready : StmtReadyConcrete Γ σ (.assign p e))
    (hstep : BigStepStmt σ (.assign p e) CtrlResult.normal σ') :
    ∃ v,
      PlaceReadyConcrete Γ σ p τ ∧
      ValueCompat v τ ∧
      Assigns σ p v σ' := by
  rcases assign_ready_data hready with ⟨τ', hp', hrp', hv', hre'⟩
  have hτ : τ' = τ := hasPlaceType_unique hp' hp
  subst hτ
  cases hstep with
  | assign hstepE hassign =>
      exact ⟨_, hrp', expr_ready_eval_compat hre' hstepE, hassign⟩

theorem blockReadyConcrete_of_openScope
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hready : BlockReadyConcrete (pushTypeScope Γ) (pushScope σ) ss)
    (hopen : OpenScope σ σ') :
    BlockReadyConcrete (pushTypeScope Γ) σ' ss := by
  have hopen_push : OpenScope σ (pushScope σ) := by
    simp [OpenScope, pushScope]
  have hEq : σ' = pushScope σ :=
    openScope_deterministic hopen hopen_push
  subst hEq
  simpa using hready

end Cpp
