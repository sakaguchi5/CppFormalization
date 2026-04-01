import CppFormalization.Cpp2.Closure.Internal.StmtControlCompatibility

namespace Cpp

/--
A thin case-library for building `normal` control compatibility.

Design intent:
- keep `stmt_normal_control_compatible` / `block_normal_control_compatible` as the only
  public normal theorems,
- keep `break` / `continue` compatibility externalized as oracles,
- extract the constructor-wise proof content from the failed monolithic mutual theorem.

This file is intentionally small and local.  It is not a new semantic layer.
-/


abbrev StmtNormalCompatCaseOracle : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI ControlKind.normalK Γ s Δ)
    (hstep : BigStepStmt σ s CtrlResult.normal σ'),
    StmtControlCompatible hty hstep

abbrev BlockNormalCompatOracle : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .normalK Γ ss Δ)
    (hstep : BigStepBlock σ ss .normal σ'),
    BlockControlCompatible hty hstep

abbrev StmtBreakCompatCaseOracle : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI ControlKind.breakK Γ s Δ)
    (hstep : BigStepStmt σ s CtrlResult.breakResult σ'),
    StmtControlCompatible hty hstep

abbrev StmtContinueCompatCaseOracle : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI ControlKind.continueK Γ s Δ)
    (hstep : BigStepStmt σ s CtrlResult.continueResult σ'),
    StmtControlCompatible hty hstep

abbrev BlockBreakCompatCaseOracle : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI ControlKind.breakK Γ ss Δ)
    (hstep : BigStepBlock σ ss CtrlResult.breakResult σ'),
    BlockControlCompatible hty hstep

abbrev BlockContinueCompatCaseOracle : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI ControlKind.continueK Γ ss Δ)
    (hstep : BigStepBlock σ ss CtrlResult.continueResult σ'),
    BlockControlCompatible hty hstep

theorem stmt_normal_seq_case
    (stmtNormal : StmtNormalCompatCaseOracle)
    {Γ Δ Θ : TypeEnv} {σ σ₁ σ' : State} {s t : CppStmt}
    (htyS : HasTypeStmtCI ControlKind.normalK Γ s Θ)
    (htyT : HasTypeStmtCI ControlKind.normalK Θ t Δ)
    (hstepS : BigStepStmt σ s CtrlResult.normal σ₁)
    (hstepT : BigStepStmt σ₁ t CtrlResult.normal σ') :
    StmtControlCompatible
      (HasTypeStmtCI.seq_normal htyS htyT)
      (BigStepStmt.seqNormal hstepS hstepT) := by
  exact .seq_normal (stmtNormal htyS hstepS) (stmtNormal htyT hstepT)

theorem stmt_normal_ite_true_case
    (stmtNormal : StmtNormalCompatCaseOracle)
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt}
    (hc : HasValueType Γ c (CppType.base BaseType.bool))
    (htyS : HasTypeStmtCI ControlKind.normalK Γ s Δ)
    (htyT : HasTypeStmtCI ControlKind.normalK Γ t Δ)
    (hcond : BigStepValue σ c (Value.bool true))
    (hstepS : BigStepStmt σ s CtrlResult.normal σ') :
    StmtControlCompatible
      (HasTypeStmtCI.ite hc htyS htyT)
      (BigStepStmt.iteTrue hcond hstepS) := by
  -- すべてを明示的に指定する場合（@を使用）
  exact @StmtControlCompatible.ite_true _ _ _ _ _ _ _ _ _ hc htyS htyT hcond hstepS (stmtNormal htyS hstepS)

theorem stmt_normal_ite_false_case
    (stmtNormal : StmtNormalCompatCaseOracle)
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt}
    (hc : HasValueType Γ c (CppType.base BaseType.bool))
    (htyS : HasTypeStmtCI ControlKind.normalK Γ s Δ)
    (htyT : HasTypeStmtCI ControlKind.normalK Γ t Δ)
    (hcond : BigStepValue σ c (Value.bool false))
    (hstepT : BigStepStmt σ t CtrlResult.normal σ') :
    StmtControlCompatible
      (HasTypeStmtCI.ite hc htyS htyT)
      (BigStepStmt.iteFalse hcond hstepT) := by
  exact @StmtControlCompatible.ite_false _ _ _ _ _ _ _ _ _ hc htyS htyT hcond hstepT (stmtNormal htyT hstepT)

theorem stmt_normal_while_false_case
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (CppType.base BaseType.bool))
    (hN : HasTypeStmtCI ControlKind.normalK Γ body Γ)
    (hB : HasTypeStmtCI ControlKind.breakK Γ body Γ)
    (hC : HasTypeStmtCI ControlKind.continueK Γ body Γ)
    (hcond : BigStepValue σ c (Value.bool false)) :
    StmtControlCompatible
      (HasTypeStmtCI.while_normal hc hN hB hC)
      (BigStepStmt.whileFalse hcond) := by
  exact StmtControlCompatible.while_false_normal (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hcond := hcond)

theorem stmt_normal_while_body_normal_case
    (stmtNormal : StmtNormalCompatCaseOracle)
    {Γ : TypeEnv} {σ σ₁ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (CppType.base BaseType.bool))
    (hN : HasTypeStmtCI ControlKind.normalK Γ body Γ)
    (hB : HasTypeStmtCI ControlKind.breakK Γ body Γ)
    (hC : HasTypeStmtCI ControlKind.continueK Γ body Γ)
    (hcond : BigStepValue σ c (Value.bool true))
    (hbody : BigStepStmt σ body CtrlResult.normal σ₁)
    (htail : BigStepStmt σ₁ (.whileStmt c body) CtrlResult.normal σ') :
    StmtControlCompatible
      (HasTypeStmtCI.while_normal hc hN hB hC)
      (BigStepStmt.whileTrueNormal hcond hbody htail) := by
  exact StmtControlCompatible.while_true_normal_normal
    (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hcond := hcond) (hbody := hbody) (htail := htail)
    (stmtNormal hN hbody)
    (stmtNormal (HasTypeStmtCI.while_normal hc hN hB hC) htail)

theorem stmt_normal_while_body_break_case
    (stmtBreak : StmtBreakCompatCaseOracle)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (CppType.base BaseType.bool))
    (hN : HasTypeStmtCI ControlKind.normalK Γ body Γ)
    (hB : HasTypeStmtCI ControlKind.breakK Γ body Γ)
    (hC : HasTypeStmtCI ControlKind.continueK Γ body Γ)
    (hcond : BigStepValue σ c (Value.bool true))
    (hbody : BigStepStmt σ body CtrlResult.breakResult σ') :
    StmtControlCompatible
      (HasTypeStmtCI.while_normal hc hN hB hC)
      (BigStepStmt.whileTrueBreak hcond hbody) := by
  exact StmtControlCompatible.while_true_break
    (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hcond := hcond) (hbody := hbody)
    (stmtBreak hB hbody)

 theorem stmt_normal_while_body_continue_case
    (stmtNormal : StmtNormalCompatCaseOracle)
    (stmtContinue : StmtContinueCompatCaseOracle)
    {Γ : TypeEnv} {σ σ₁ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (CppType.base BaseType.bool))
    (hN : HasTypeStmtCI ControlKind.normalK Γ body Γ)
    (hB : HasTypeStmtCI ControlKind.breakK Γ body Γ)
    (hC : HasTypeStmtCI ControlKind.continueK Γ body Γ)
    (hcond : BigStepValue σ c (Value.bool true))
    (hbody : BigStepStmt σ body CtrlResult.continueResult σ₁)
    (htail : BigStepStmt σ₁ (.whileStmt c body) CtrlResult.normal σ') :
    StmtControlCompatible
      (HasTypeStmtCI.while_normal hc hN hB hC)
      (BigStepStmt.whileTrueContinue hcond hbody htail) := by
  exact StmtControlCompatible.while_true_continue_normal
    (hc := hc) (hN := hN) (hB := hB) (hC := hC)
    (hcond := hcond) (hbody := hbody) (htail := htail)
    (stmtContinue hC hbody)
    (stmtNormal (HasTypeStmtCI.while_normal hc hN hB hC) htail)

theorem stmt_normal_block_case
    (blockNormal : BlockNormalCompatOracle)
    {Γ Θ : TypeEnv} {σ σ₀ σ_body_end σ_final : State} {ss : StmtBlock} -- 引数を追加・変更
    (htyBody : HasTypeBlockCI ControlKind.normalK (pushTypeScope Γ) ss Θ)
    (hopen : OpenScope σ σ₀)
    (hbody : BigStepBlock σ₀ ss CtrlResult.normal σ_body_end)
    (hclose : CloseScope σ_body_end σ_final) : -- σ' σ' から変更
    StmtControlCompatible
      (HasTypeStmtCI.block htyBody)
      (BigStepStmt.block hopen hbody hclose) := by
  -- StmtControlCompatible.block コンストラクタを適用
  exact StmtControlCompatible.block
    (htyB := htyBody)
    (hopen := hopen)
    (hbody := hbody)
    (hclose := hclose)
    -- blockNormal オラクル（再帰呼び出しの結果）を渡す
    (blockNormal htyBody hbody)

theorem block_normal_nil_case
    {Γ : TypeEnv} {σ : State} :
    BlockControlCompatible
      (HasTypeBlockCI.nil (Γ := Γ))
      (BigStepBlock.nil (σ := σ)) := by
  exact BlockControlCompatible.nil (Γ := Γ) (σ := σ)

theorem block_normal_cons_case
    (stmtNormal : StmtNormalCompatCaseOracle)
    (blockNormal : BlockNormalCompatOracle)
    {Γ Δ Θ : TypeEnv} {σ σ₁ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (htyS : HasTypeStmtCI ControlKind.normalK Γ s Θ)
    (htyT : HasTypeBlockCI ControlKind.normalK Θ ss Δ)
    (hstepS : BigStepStmt σ s CtrlResult.normal σ₁)
    (hstepT : BigStepBlock σ₁ ss CtrlResult.normal σ') :
    BlockControlCompatible
      (HasTypeBlockCI.cons_normal htyS htyT)
      (BigStepBlock.consNormal hstepS hstepT) := by
  exact BlockControlCompatible.cons_normal
    (htyS := htyS) (htyT := htyT) (hstepS := hstepS) (hstepT := hstepT)
    (stmtNormal htyS hstepS)
    (blockNormal htyT hstepT)

end Cpp
