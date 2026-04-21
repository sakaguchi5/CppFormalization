import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.ReadinessInversions
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReentryKernelFacts
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

/-- while compatibility branch が必要とする局所文脈。 -/
structure WhileCompatCtx
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  condReady : ExprReadyConcrete Γ σ c (.base .bool)
  bodyBoundary : LoopBodyBoundaryCI Γ σ body
  reentry : LoopReentryKernelCI Γ c body

abbrev WhileCtxProvider : Type :=
  ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt},
    HasValueType Γ c (.base .bool) →
    HasTypeStmtCI .normalK Γ body Γ →
    HasTypeStmtCI .breakK Γ body Γ →
    HasTypeStmtCI .continueK Γ body Γ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    WhileCompatCtx Γ σ c body

def whileCtxOf
    (mkWhileCtx : WhileCtxProvider)
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hsc : ScopedTypedStateConcrete Γ σ)
    (hreadyWhile : StmtReadyConcrete Γ σ (.whileStmt c body)) :
    WhileCompatCtx Γ σ c body :=
  mkWhileCtx hc hN hB hC hsc hreadyWhile

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
    (mkWhileCtx : WhileCtxProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hsc : ScopedTypedStateConcrete Γ σ)
    (hreadyWhile : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hbody : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  let wctx := whileCtxOf mkWhileCtx hc hN hB hC hsc hreadyWhile
  exact while_ready_after_body_normal_of_kernel
    wctx.reentry
    wctx.condReady
    wctx.bodyBoundary
    hbody

theorem whileTailReadyContinue
    (mkWhileCtx : WhileCtxProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hN : HasTypeStmtCI .normalK Γ body Γ)
    (hB : HasTypeStmtCI .breakK Γ body Γ)
    (hC : HasTypeStmtCI .continueK Γ body Γ)
    (hsc : ScopedTypedStateConcrete Γ σ)
    (hreadyWhile : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hbody : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  let wctx := whileCtxOf mkWhileCtx hc hN hB hC hsc hreadyWhile
  exact while_ready_after_body_continue_of_kernel
    wctx.reentry
    wctx.condReady
    wctx.bodyBoundary
    hbody

theorem whileNormalNormalCase
    (mkWhileCtx : WhileCtxProvider)
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
    whileTailReadyNormal mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody
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
    (mkWhileCtx : WhileCtxProvider)
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
    whileTailReadyContinue mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody
  exact ihTail hsc1 hreadyTail

theorem whileNormalReturnCase
    (mkWhileCtx : WhileCtxProvider)
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
    whileTailReadyNormal mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody
  exact ihTail hsc1 hreadyTail

theorem whileContinueReturnCase
    (mkWhileCtx : WhileCtxProvider)
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
    whileTailReadyContinue mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody
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
