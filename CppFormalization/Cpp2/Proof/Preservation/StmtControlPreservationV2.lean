--import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
--import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ConditionalNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.WhileNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Closure.Transitions.Minor.OpenScopeDecomposition
import CppFormalization.Cpp2.Lemmas.TransitionDeterminism
import CppFormalization.Cpp2.Lemmas.ExprTypeUniqueness
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernelSupport
namespace Cpp

/-!

-/

theorem stmt_control_preserves_scoped_typed_state_of_compatible_core
    (mkWhileCtx : WhileCtxProvider)
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  refine
    StmtControlCompatible.rec
      (motive_1 := fun
        {k Γ Δ s σ ctrl σ'}
        (hty : HasTypeStmtCI k Γ s Δ)
        (hstep : BigStepStmt σ s ctrl σ')
        (_ : StmtControlCompatible hty hstep) =>
          ScopedTypedStateConcrete Γ σ →
          StmtReadyConcrete Γ σ s →
          ScopedTypedStateConcrete Δ σ')
      (motive_2 := fun
        {k Γ Δ ss σ ctrl σ'}
        (hty : HasTypeBlockCI k Γ ss Δ)
        (hstep : BigStepBlock σ ss ctrl σ')
        (_ : BlockControlCompatible hty hstep) =>
          ScopedTypedStateConcrete Γ σ →
          BlockReadyConcrete Γ σ ss →
          ScopedTypedStateConcrete Δ σ')
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_
      hcomp
  · -- skip
    intro _ _ Γ σ hsc hready
    exact hsc
  · -- exprStmt
    intro Γ σ e τ hv hstep hsc hready
    simpa using hsc
  · -- assign
    intro Γ σ σ' p e τ hp hv hstep hsc hready
    rcases assign_preservation_inputs hp hready hstep with
      ⟨v, hrp, hvcompat, hassign⟩
    exact assigns_preserves_scoped_typed_state_concrete
      hsc hp hrp hvcompat hassign
  · -- declareObjNone
    intro Γ σ σ' τ x hfresh hobj hstep hsc hready
    cases hstep with
    | declareObjNone hdecl =>
        exact declares_object_preserves_scoped_typed_state_concrete
           hfresh hsc hdecl
  · -- declareObjSome
    intro Γ σ σ' τ x e hfresh hobj hv hstep hsc hready
    cases hready with
    | declareObjSome hobj' hfresh' hv' hre =>
        cases hstep with
        | declareObjSome hstepE hdecl =>
        exact declares_object_preserves_scoped_typed_state_concrete
           hfresh hsc hdecl
  · -- declareRef
    intro Γ σ σ' τ x p hfresh hp hstep hsc hready
    cases hstep with
    | declareRef hplace hdecl =>
      exact declares_ref_preserves_scoped_typed_state_concrete
        hfresh hsc hdecl
  · -- breakStmt
    intro _ _ Γ σ hsc hready
    simpa using hsc
  · -- continueStmt
    intro _ _ Γ σ hsc hready
    simpa using hsc
  · -- returnNone
    intro _ _ Γ σ hsc hready
    simpa using hsc
  · -- returnSome
    intro Γ σ e τ rv hv hstep hsc hready
    simpa using hsc
  · -- seq_normal
    intro k Γ Θ Δ s t σ σ₁ σ₂ ctrl
      htyS htyT hstepS hstepT
      hcompS hcompT
      ihS ihT
      hsc hready

    have hreadyS : StmtReadyConcrete Γ σ s :=
      seq_ready_left hready

    have hsc₁ : ScopedTypedStateConcrete Θ σ₁ :=
      ihS hsc hreadyS

    have hreadyT : StmtReadyConcrete Θ σ₁ t :=
      seq_ready_right_after_left_normal htyS hsc₁ hready hstepS

    exact ihT hsc₁ hreadyT
  · -- seq_break
    -- 引数の数は 11個。最後から2番目が IH (関数)、最後が ScopedTypedStateConcrete
    intro k_br Γ_env Δ_env s_stmt t_stmt σ_st σ_final hty_s hstep_s hcomp_s ihS hsc_in
    -- 最後にゴールにある StmtReadyConcrete を intro する
    intro hready_seq
    -- 1. seq_ready_left を適用。
    -- ここで `Γ_env` は TypeEnv なので、これを使えば mismatch は起きません。
    have hreadyS : StmtReadyConcrete Γ_env σ_st s_stmt := seq_ready_left hready_seq
    -- 2. ihS を適用。
    -- ihS の型は (ScopedTypedStateConcrete -> StmtReadyConcrete -> ScopedTypedStateConcrete)
    -- となっているので、hsc_in と hreadyS を渡します。
    exact ihS hsc_in hreadyS
  · -- seq_continue
    intro k_ct Γ_env Δ_env s_stmt t_stmt σ_st σ_final hty_s hstep_s hcomp_s ihS hsc_in
    intro hready_seq
    have hreadyS : StmtReadyConcrete Γ_env σ_st s_stmt := seq_ready_left hready_seq
    exact ihS hsc_in hreadyS

  · -- seq_return
    intro k_rt Γ_env Δ_env s_stmt t_stmt σ_st σ_final rv hty_s hstep_s hcomp_s ihS hsc_in
    intro hready_seq
    have hreadyS : StmtReadyConcrete Γ_env σ_st s_stmt := seq_ready_left hready_seq
    exact ihS hsc_in hreadyS
  · -- ite_true
    intro k Γ Δ c s t σ σ' ctrl hc htyS htyT hcond hstepS hcompS ihS hsc hready
    cases hready with
    | ite hc' hcondReady hreadyS hreadyT =>
        exact ihS hsc hreadyS

  · -- ite_false
    intro k Γ Δ c s t σ σ' ctrl hc htyS htyT hcond hstepT hcompT ihT hsc hready
    cases hready with
    | ite hc' hcondReady hreadyS hreadyT =>
        exact ihT hsc hreadyT
  · -- while_false_normal
    intro Γ σ c body hc hN hB hC hcond hsc_in hreadyWhile
    simpa using hsc_in

  · -- while_true_normal_normal
    intro Γ σ0 σ1 σ2 c body hc hN hB hC hcond hbody htail
      hcompBody hcompTail ihBody ihTail hsc_in
    intro hreadyWhile

    have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
      whileBodyConcrete ihBody hsc_in hreadyWhile

    have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
      whileTailReadyNormal mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody

    exact ihTail hsc1 hreadyTail

  · -- while_true_break
    intro Γ σ0 σ1 c body hc hN hB hC hcond hbody hcompBody ihBody hsc_in
    intro hreadyWhile

    have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
      whileBodyConcrete ihBody hsc_in hreadyWhile

    simpa using hsc1

  · -- while_true_continue_normal
    intro Γ σ0 σ1 σ2 c body hc hN hB hC hcond hbody htail
      hcompBody hcompTail ihBody ihTail hsc_in
    intro hreadyWhile

    have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
      whileBodyConcrete ihBody hsc_in hreadyWhile

    have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
      whileTailReadyContinue mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody

    exact ihTail hsc1 hreadyTail

  · -- while_true_normal_return
    intro Γ Δ σ0 σ1 σ2 c body rv_opt hc_val hN_st hB_st hC_st hR_st hcond_val hbody htail
      hcompBody hcompTail ihBody ihTail hsc_in
    intro hreadyWhile

    -- recursor の binder 順が読みにくいので、ここで意味のある名前へ束縛し直す
    have hc : HasValueType Γ c (.base .bool) := rv_opt
    have hN : HasTypeStmtCI .normalK Γ body Γ := hc_val
    have hB : HasTypeStmtCI .breakK Γ body Γ := hN_st
    have hC : HasTypeStmtCI .continueK Γ body Γ := hB_st

    have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
      whileBodyConcrete ihBody hsc_in hreadyWhile

    have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
      whileTailReadyNormal mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody

    exact ihTail hsc1 hreadyTail

  · -- while_true_continue_return
    intro Γ Δ σ0 σ1 σ2 c body rv_opt hc_val hN_st hB_st hC_st hR_st hcond_val hbody htail
      hcompBody hcompTail ihBody ihTail hsc_in
    intro hreadyWhile

    have hc : HasValueType Γ c (.base .bool) := rv_opt
    have hN : HasTypeStmtCI .normalK Γ body Γ := hc_val
    have hB : HasTypeStmtCI .breakK Γ body Γ := hN_st
    have hC : HasTypeStmtCI .continueK Γ body Γ := hB_st

    have hsc1 : ScopedTypedStateConcrete Γ σ1 :=
      whileBodyConcrete ihBody hsc_in hreadyWhile

    have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
      whileTailReadyContinue mkWhileCtx hc hN hB hC hsc_in hreadyWhile hbody

    exact ihTail hsc1 hreadyTail

  · -- while_true_return
    intro Γ Δ σ0 σ1 c body rv hc hN hB hC hR hcond hbody hcompBody ihBody hsc_in
    intro hreadyWhile

    have hreadyBody : StmtReadyConcrete Γ σ0 body :=
      while_ready_body_data hreadyWhile

    have hsc1 : ScopedTypedStateConcrete Δ σ1 :=
      ihBody hsc_in hreadyBody

    simpa using hsc1
  · -- block
    intro k_blk Γ_env Θ_env ss_blk σ_in σ_open σ_body σ_out ctrl
      htyBlk hopen hbody hclose
      hcompBlk ihBlk
      hsc_in
    intro hready_block

    cases hready_block with
    | block hreadyBody_old =>
        -- 1. OpenScope の性質を利用して整合性を示す (ここはOK)
        have hsc_open : ScopedTypedStateConcrete (pushTypeScope Γ_env) σ_open :=
          openScope_preserves_scoped_typed_state_concrete hsc_in hopen

        -- 2. 【重要】hreadyBody_old の状態 (pushScope σ_in) を σ_open に書き換える
        -- a.lean または Readiness.lean にある OpenScope と Readiness の関係を示す補題を使います
        have hreadyBody : BlockReadyConcrete (pushTypeScope Γ_env) σ_open ss_blk :=
          blockReadyConcrete_of_openScope hreadyBody_old hopen

        -- 3. 状態が一致したので ihBlk が呼べるようになります
        have hsc_body : ScopedTypedStateConcrete Θ_env σ_body :=
          ihBlk hsc_open hreadyBody

        -- 4. 最後に CloseScope で外側の整合性を復元
        have hExt : TopFrameExtensionOf Γ_env Θ_env :=
          block_ci_topFrameExtension htyBlk

        exact closeScope_preserves_outer_from_topFrameExtension
          hExt hsc_body hclose
  · -- nil
    intro _ _ Γ σ hsc hready
    simpa using hsc
  · -- cons_normal
    intro k Γ Θ Δ s ss σ σ₁ σ₂ ctrl
      htyS htyT hstepS hstepT
      hcompS hcompT
      ihS ihT
      hsc hready

    have hreadyHead : StmtReadyConcrete Γ σ s :=
      cons_block_ready_head hready

    have hsc₁ : ScopedTypedStateConcrete Θ σ₁ :=
      ihS hsc hreadyHead

    have hreadyTail : BlockReadyConcrete Θ σ₁ ss :=
      cons_block_ready_tail_after_head_normal htyS hsc₁ hready hstepS

    exact ihT hsc₁ hreadyTail

  · -- cons_break
    -- 1. rec から渡される引数を、意味ではなく「型」の並び順で正確に受け取る
    -- (htyS, hstepS, hcompS, ihS, hsc_in) の順で並んでいるはずです
    intro Γ_blk Δ_env s_env ss_stmt σ_blk σ_st σ_final htyS hstepS hcompS ihS hsc_in

    intro hready_block_all

    have hreadyHead : StmtReadyConcrete Δ_env σ_st ss_stmt :=
      cons_block_ready_head hready_block_all

    exact ihS hsc_in hreadyHead

  · -- cons_continue
    intro Γ_blk Δ_env s_env ss_stmt σ_blk σ_st σ_final htyS hstepS hcompS ihS hsc_in
    intro hready_block_all
    have hreadyHead : StmtReadyConcrete Δ_env σ_st ss_stmt :=
      cons_block_ready_head hready_block_all
    exact ihS hsc_in hreadyHead

  · -- cons_return
    intro Γ_blk Δ_env s_env ss_stmt σ_blk σ_st σ_final rv htyS hstepS hcompS ihS hsc_in
    intro hready_block_all
    have hreadyHead : StmtReadyConcrete Δ_env σ_st ss_stmt :=
      cons_block_ready_head hready_block_all
    exact ihS hsc_in hreadyHead



end Cpp
