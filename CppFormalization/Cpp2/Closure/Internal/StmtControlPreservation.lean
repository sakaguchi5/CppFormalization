import CppFormalization.Cpp2.Closure.Internal.StmtControlKernel
import CppFormalization.Cpp2.Closure.Internal.StmtAbruptCompatibility

namespace Cpp

/-
標準証明様式（control-aware big-step 層）

この層では、break / continue / while により control flow が back-edge を持つため、
Stmt / Block の構文サイズに基づく再帰を主証明原理にしてはならない。
特に whileTrueNormal / whileTrueContinue の tail は同じ while 文へ戻るため、
syntax-size recursion は本質的に不適切である。

採用する標準形は以下である。

1. 主語は構文ではなく実行導出とする。
   - statement 側: BigStepStmt
   - block 側: BigStepBlock

2. 直接公開 claim を recursor の motive にせず、
   高階適用を外に漏らさない bundle 形にまとめる。
   例: normal / break / continue 各 control に対応する compatibility 成分を束ねる。

3. 証明本体は mutual recursor による相互消去で書く。
   - stmt 導出の子導出と block 導出の子導出の両方に IH を持つ
   - while tail は「同じ文」ではあるが「strict subderivation」であることを使う

4. recursor で作った bundle から、最後に公開 claim / theorem に降ろす。
   これにより公開 API は単純化され、内部の motive 設計を隠蔽できる。

5. control preservation / closure / invariant 系の将来の定理も、
   原則としてこの bundle + mutual recursor + claim 降下の形で作る。
   syntax-size recursion に戻らないこと。
-/


private structure StmtCompatBundle
    {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ s ctrl σ') : Prop where
  normalPart :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .normalK Γ s Δ),
          StmtControlCompatible hty hstep
    | _ => True
  breakPart :
    match ctrl with
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .breakK Γ s Δ),
          StmtControlCompatible hty hstep
    | _ => True
  continuePart :
    match ctrl with
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .continueK Γ s Δ),
          StmtControlCompatible hty hstep
    | _ => True

private structure BlockCompatBundle
    {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepBlock σ ss ctrl σ') : Prop where
  normalPart :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .normalK Γ ss Δ),
          BlockControlCompatible hty hstep
    | _ => True
  breakPart :
    match ctrl with
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .breakK Γ ss Δ),
          BlockControlCompatible hty hstep
    | _ => True
  continuePart :
    match ctrl with
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .continueK Γ ss Δ),
          BlockControlCompatible hty hstep
    | _ => True

theorem stmt_bundle_to_claim
    {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hb : StmtCompatBundle hstep) :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .normalK Γ s Δ),
          StmtControlCompatible hty hstep
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .breakK Γ s Δ),
          StmtControlCompatible hty hstep
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .continueK Γ s Δ),
          StmtControlCompatible hty hstep
    | .returnResult _ => True := by
  cases ctrl with
  | normal =>
      intro Γ Δ hty
      exact hb.normalPart hty
  | breakResult =>
      intro Γ Δ hty
      exact hb.breakPart hty
  | continueResult =>
      intro Γ Δ hty
      exact hb.continuePart hty
  | returnResult rv =>
      trivial

theorem block_bundle_to_claim
    {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hb : BlockCompatBundle hstep) :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .normalK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .breakK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .continueK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .returnResult _ => True := by
  cases ctrl with
  | normal =>
      intro Γ Δ hty
      exact hb.normalPart hty
  | breakResult =>
      intro Γ Δ hty
      exact hb.breakPart hty
  | continueResult =>
      intro Γ Δ hty
      exact hb.continuePart hty
  | returnResult rv =>
      trivial

theorem stmt_compat_bundle
    {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ s ctrl σ') :
    StmtCompatBundle hstep := by
  exact
    BigStepStmt.rec
      (motive_1 := fun {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
        (h : BigStepStmt σ s ctrl σ') => StmtCompatBundle h)
      (motive_2 := fun {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
        (h : BigStepBlock σ ss ctrl σ') => BlockCompatBundle h)
      (skip := by
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | skip => exact .skip (Γ := Γ) (σ := σ)
        · trivial
        · trivial)
      (expr := by
        intro σ e v hval
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | exprStmt hv => exact .exprStmt (hv := hv)
        · trivial
        · trivial)
      (assign := by
        intro σ σ' p e v hval hassign
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | assign hp hv => exact .assign (hp := hp) (hv := hv)
        · trivial
        · trivial)
      (declareObjNone := by
        intro σ σ' τ x hdecl
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | declareObjNone hfresh hobj => exact .declareObjNone (hfresh := hfresh) (hobj := hobj)
        · trivial
        · trivial)
      (declareObjSome := by
        intro σ σ' τ x e v hval hdecl
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | declareObjSome hfresh hobj hv =>
              exact .declareObjSome (hfresh := hfresh) (hobj := hobj) (hv := hv)
        · trivial
        · trivial)
      (declareRef := by
        intro σ σ' τ x p a hplace href
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | declareRef hfresh hp => exact .declareRef (hfresh := hfresh) (hp := hp)
        · trivial
        · trivial)
      (seqNormal := by
        intro σ σ₁ σ₂ s t ctrl hstepS hstepT ihS ihT
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | seq_normal htyS htyT =>
                  exact .seq_normal (ihS.normalPart htyS) (ihT.normalPart htyT)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | seq_break htyS =>
                  exfalso
                  exact stmt_break_no_normal_step htyS hstepS
              | seq_normal htyS htyT =>
                  exact .seq_normal (ihS.normalPart htyS) (ihT.breakPart htyT)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | seq_continue htyS =>
                  exfalso
                  exact stmt_continue_no_normal_step htyS hstepS
              | seq_normal htyS htyT =>
                  exact .seq_normal (ihS.normalPart htyS) (ihT.continuePart htyT)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (seqBreak := by
        intro σ σ₁ s t hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · intro Γ Δ hty
          cases hty with
          | seq_break htyS =>
              exact StmtControlCompatible.seq_break (t := t) (ihS.breakPart htyS)
          | seq_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_break_step htyS hstepS
        · trivial)
      (seqContinue := by
        intro σ σ₁ s t hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · trivial
        · intro Γ Δ hty
          cases hty with
          | seq_continue htyS =>
              exact .seq_continue (t := t) (ihS.continuePart htyS)
          | seq_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_continue_step htyS hstepS)
      (seqReturn := by
        intro σ σ₁ s t rv hstepS ihS
        exact ⟨trivial, trivial, trivial⟩)
      (iteTrue := by
        intro σ σ' c s t ctrl hcond hstepS ihS
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepS := hstepS) (ihS.normalPart htyS)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepS := hstepS) (ihS.breakPart htyS)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepS := hstepS) (ihS.continuePart htyS)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (iteFalse := by
        intro σ σ' c s t ctrl hcond hstepT ihT
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepT := hstepT) (ihT.normalPart htyT)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepT := hstepT) (ihT.breakPart htyT)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepT := hstepT) (ihT.continuePart htyT)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (whileFalse := by
        intro σ c body hcond
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | while_normal hc hN hB hC =>
              exact .while_false_normal (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hcond := hcond)
        · trivial
        · trivial)
      (whileTrueNormal := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | while_normal hc hN hB hC =>
                  exact .while_true_normal_normal
                    (hc := hc) (hN := hN) (hB := hB) (hC := hC)
                    (hcond := hcond) (hbody := hbody) (htail := htail)
                    (ihBody.normalPart hN)
                    (ihTail.normalPart (HasTypeStmtCI.while_normal hc hN hB hC))
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (whileTrueBreak := by
        intro σ σ₁ c body hcond hbody ihBody
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | while_normal hc hN hB hC =>
              exact .while_true_break
                (hc := hc) (hN := hN) (hB := hB) (hC := hC)
                (hcond := hcond) (hbody := hbody)
                (ihBody.breakPart hB)
        · trivial
        · trivial)
      (whileTrueContinue := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | while_normal hc hN hB hC =>
                  exact .while_true_continue_normal
                    (hc := hc) (hN := hN) (hB := hB) (hC := hC)
                    (hcond := hcond) (hbody := hbody) (htail := htail)
                    (ihBody.continuePart hC)
                    (ihTail.normalPart (HasTypeStmtCI.while_normal hc hN hB hC))
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (whileTrueReturn := by
        intro σ σ₁ c body rv hcond hbody ihBody
        exact ⟨trivial, trivial, trivial⟩)
      (block := by
        intro σ σ₀ σ₁ σ₂ ss ctrl hopen hbody hclose ihBody
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | block hExt htyB =>
                  exact .block
                    (hExt := hExt) (htyB := htyB)
                    (hopen := hopen) (hbody := hbody) (hclose := hclose)
                    (ihBody.normalPart htyB)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | block hExt htyB =>
                  exact .block
                    (hExt := hExt) (htyB := htyB)
                    (hopen := hopen) (hbody := hbody) (hclose := hclose)
                    (ihBody.breakPart htyB)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | block hExt htyB =>
                  exact .block
                    (hExt := hExt) (htyB := htyB)
                    (hopen := hopen) (hbody := hbody) (hclose := hclose)
                    (ihBody.continuePart htyB)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (breakStmt := by
        intro σ
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · intro Γ Δ hty
          cases hty with
          | breakStmt => exact .breakStmt (Γ := Γ) (σ := σ)
        · trivial)
      (continueStmt := by
        intro σ
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · trivial
        · intro Γ Δ hty
          cases hty with
          | continueStmt => exact .continueStmt (Γ := Γ) (σ := σ))
      (returnNoneStmt := by
        intro σ
        exact ⟨trivial, trivial, trivial⟩)
      (returnSome := by
        intro σ e v hval
        exact ⟨trivial, trivial, trivial⟩)
      (nil := by
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | nil => exact .nil (Γ := Γ) (σ := σ)
        · trivial
        · trivial)
      (consNormal := by
        intro σ σ₁ σ₂ s ss ctrl hstepS hstepT ihS ihT
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | cons_normal htyS htyT =>
                  exact .cons_normal (ihS.normalPart htyS) (ihT.normalPart htyT)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | cons_break htyS =>
                  exfalso
                  exact stmt_break_no_normal_step htyS hstepS
              | cons_normal htyS htyT =>
                  exact .cons_normal (ihS.normalPart htyS) (ihT.breakPart htyT)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | cons_continue htyS =>
                  exfalso
                  exact stmt_continue_no_normal_step htyS hstepS
              | cons_normal htyS htyT =>
                  exact .cons_normal (ihS.normalPart htyS) (ihT.continuePart htyT)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (consBreak := by
        intro σ σ₁ s ss hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · intro Γ Δ hty
          cases hty with
          | cons_break htyS =>
              exact .cons_break (ss := ss) (ihS.breakPart htyS)
          | cons_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_break_step htyS hstepS
        · trivial)
      (consContinue := by
        intro σ σ₁ s ss hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · trivial
        · intro Γ Δ hty
          cases hty with
          | cons_continue htyS =>
              exact .cons_continue (ss := ss) (ihS.continuePart htyS)
          | cons_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_continue_step htyS hstepS)
      (consReturn := by
        intro σ σ₁ s ss rv hstepS ihS
        exact ⟨trivial, trivial, trivial⟩)
      hstep

theorem block_compat_bundle
    {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepBlock σ ss ctrl σ') :
    BlockCompatBundle hstep := by
  exact
    BigStepBlock.rec
      (motive_1 := fun {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
        (h : BigStepStmt σ s ctrl σ') => StmtCompatBundle h)
      (motive_2 := fun {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
        (h : BigStepBlock σ ss ctrl σ') => BlockCompatBundle h)
      (skip := by
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | skip => exact .skip (Γ := Γ) (σ := σ)
        · trivial
        · trivial)
      (expr := by
        intro σ e v hval
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | exprStmt hv => exact .exprStmt (hv := hv)
        · trivial
        · trivial)
      (assign := by
        intro σ σ' p e v hval hassign
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | assign hp hv => exact .assign (hp := hp) (hv := hv)
        · trivial
        · trivial)
      (declareObjNone := by
        intro σ σ' τ x hdecl
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | declareObjNone hfresh hobj => exact .declareObjNone (hfresh := hfresh) (hobj := hobj)
        · trivial
        · trivial)
      (declareObjSome := by
        intro σ σ' τ x e v hval hdecl
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | declareObjSome hfresh hobj hv =>
              exact .declareObjSome (hfresh := hfresh) (hobj := hobj) (hv := hv)
        · trivial
        · trivial)
      (declareRef := by
        intro σ σ' τ x p a hplace href
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | declareRef hfresh hp => exact .declareRef (hfresh := hfresh) (hp := hp)
        · trivial
        · trivial)
      (seqNormal := by
        intro σ σ₁ σ₂ s t ctrl hstepS hstepT ihS ihT
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | seq_normal htyS htyT =>
                  exact .seq_normal (ihS.normalPart htyS) (ihT.normalPart htyT)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | seq_break htyS =>
                  exfalso
                  exact stmt_break_no_normal_step htyS hstepS
              | seq_normal htyS htyT =>
                  exact .seq_normal (ihS.normalPart htyS) (ihT.breakPart htyT)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | seq_continue htyS =>
                  exfalso
                  exact stmt_continue_no_normal_step htyS hstepS
              | seq_normal htyS htyT =>
                  exact .seq_normal (ihS.normalPart htyS) (ihT.continuePart htyT)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (seqBreak := by
        intro σ σ₁ s t hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · intro Γ Δ hty
          cases hty with
          | seq_break htyS => exact .seq_break (t := t) (ihS.breakPart htyS)
          | seq_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_break_step htyS hstepS
        · trivial)
      (seqContinue := by
        intro σ σ₁ s t hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · trivial
        · intro Γ Δ hty
          cases hty with
          | seq_continue htyS => exact .seq_continue (t := t) (ihS.continuePart htyS)
          | seq_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_continue_step htyS hstepS)
      (seqReturn := by
        intro σ σ₁ s t rv hstepS ihS
        exact ⟨trivial, trivial, trivial⟩)
      (iteTrue := by
        intro σ σ' c s t ctrl hcond hstepS ihS
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepS := hstepS) (ihS.normalPart htyS)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepS := hstepS) (ihS.breakPart htyS)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepS := hstepS) (ihS.continuePart htyS)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (iteFalse := by
        intro σ σ' c s t ctrl hcond hstepT ihT
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepT := hstepT) (ihT.normalPart htyT)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepT := hstepT) (ihT.breakPart htyT)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | ite hc htyS htyT =>
                  exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond)
                    (hstepT := hstepT) (ihT.continuePart htyT)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (whileFalse := by
        intro σ c body hcond
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | while_normal hc hN hB hC =>
              exact .while_false_normal (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hcond := hcond)
        · trivial
        · trivial)
      (whileTrueNormal := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | while_normal hc hN hB hC =>
                  exact .while_true_normal_normal
                    (hc := hc) (hN := hN) (hB := hB) (hC := hC)
                    (hcond := hcond) (hbody := hbody) (htail := htail)
                    (ihBody.normalPart hN)
                    (ihTail.normalPart (HasTypeStmtCI.while_normal hc hN hB hC))
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (whileTrueBreak := by
        intro σ σ₁ c body hcond hbody ihBody
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | while_normal hc hN hB hC =>
              exact .while_true_break
                (hc := hc) (hN := hN) (hB := hB) (hC := hC)
                (hcond := hcond) (hbody := hbody)
                (ihBody.breakPart hB)
        · trivial
        · trivial)
      (whileTrueContinue := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | while_normal hc hN hB hC =>
                  exact .while_true_continue_normal
                    (hc := hc) (hN := hN) (hB := hB) (hC := hC)
                    (hcond := hcond) (hbody := hbody) (htail := htail)
                    (ihBody.continuePart hC)
                    (ihTail.normalPart (HasTypeStmtCI.while_normal hc hN hB hC))
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (whileTrueReturn := by
        intro σ σ₁ c body rv hcond hbody ihBody
        exact ⟨trivial, trivial, trivial⟩)
      (block := by
        intro σ σ₀ σ₁ σ₂ ss ctrl hopen hbody hclose ihBody
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | block hExt htyB =>
                  exact .block
                    (hExt := hExt) (htyB := htyB)
                    (hopen := hopen) (hbody := hbody) (hclose := hclose)
                    (ihBody.normalPart htyB)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | block hExt htyB =>
                  exact .block
                    (hExt := hExt) (htyB := htyB)
                    (hopen := hopen) (hbody := hbody) (hclose := hclose)
                    (ihBody.breakPart htyB)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | block hExt htyB =>
                  exact .block
                    (hExt := hExt) (htyB := htyB)
                    (hopen := hopen) (hbody := hbody) (hclose := hclose)
                    (ihBody.continuePart htyB)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (breakStmt := by
        intro σ
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · intro Γ Δ hty
          cases hty with
          | breakStmt => exact .breakStmt (Γ := Γ) (σ := σ)
        · trivial)
      (continueStmt := by
        intro σ
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · trivial
        · intro Γ Δ hty
          cases hty with
          | continueStmt => exact .continueStmt (Γ := Γ) (σ := σ))
      (returnNoneStmt := by
        intro σ
        exact ⟨trivial, trivial, trivial⟩)
      (returnSome := by
        intro σ e v hval
        exact ⟨trivial, trivial, trivial⟩)
      (nil := by
        refine ⟨?_, ?_, ?_⟩
        · intro Γ Δ hty
          cases hty with
          | nil => exact .nil (Γ := Γ) (σ := σ)
        · trivial
        · trivial)
      (consNormal := by
        intro σ σ₁ σ₂ s ss ctrl hstepS hstepT ihS ihT
        cases ctrl with
        | normal =>
            refine ⟨?_, ?_, ?_⟩
            · intro Γ Δ hty
              cases hty with
              | cons_normal htyS htyT =>
                  exact .cons_normal (ihS.normalPart htyS) (ihT.normalPart htyT)
            · trivial
            · trivial
        | breakResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · intro Γ Δ hty
              cases hty with
              | cons_break htyS =>
                  exfalso
                  exact stmt_break_no_normal_step htyS hstepS
              | cons_normal htyS htyT =>
                  exact .cons_normal (ihS.normalPart htyS) (ihT.breakPart htyT)
            · trivial
        | continueResult =>
            refine ⟨?_, ?_, ?_⟩
            · trivial
            · trivial
            · intro Γ Δ hty
              cases hty with
              | cons_continue htyS =>
                  exfalso
                  exact stmt_continue_no_normal_step htyS hstepS
              | cons_normal htyS htyT =>
                  exact .cons_normal (ihS.normalPart htyS) (ihT.continuePart htyT)
        | returnResult rv =>
            exact ⟨trivial, trivial, trivial⟩)
      (consBreak := by
        intro σ σ₁ s ss hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · intro Γ Δ hty
          cases hty with
          | cons_break htyS => exact .cons_break (ss := ss) (ihS.breakPart htyS)
          | cons_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_break_step htyS hstepS
        · trivial)
      (consContinue := by
        intro σ σ₁ s ss hstepS ihS
        refine ⟨?_, ?_, ?_⟩
        · trivial
        · trivial
        · intro Γ Δ hty
          cases hty with
          | cons_continue htyS => exact .cons_continue (ss := ss) (ihS.continuePart htyS)
          | cons_normal htyS htyT =>
              exfalso
              exact stmt_normal_no_continue_step htyS hstepS)
      (consReturn := by
        intro σ σ₁ s ss rv hstepS ihS
        exact ⟨trivial, trivial, trivial⟩)
      hstep

theorem stmt_compat_claim
    {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ s ctrl σ') :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .normalK Γ s Δ),
          StmtControlCompatible hty hstep
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .breakK Γ s Δ),
          StmtControlCompatible hty hstep
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .continueK Γ s Δ),
          StmtControlCompatible hty hstep
    | .returnResult _ => True := by
  have hb : StmtCompatBundle hstep := stmt_compat_bundle hstep
  cases ctrl with
  | normal =>
      intro Γ Δ hty
      exact (stmt_bundle_to_claim hb) hty
  | breakResult =>
      intro Γ Δ hty
      exact (stmt_bundle_to_claim hb) hty
  | continueResult =>
      intro Γ Δ hty
      exact (stmt_bundle_to_claim hb) hty
  | returnResult rv =>
      trivial

theorem block_compat_claim
    {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepBlock σ ss ctrl σ') :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .normalK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .breakK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .continueK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .returnResult _ => True := by
  have hb : BlockCompatBundle hstep := block_compat_bundle hstep
  cases ctrl with
  | normal =>
      intro Γ Δ hty
      exact (block_bundle_to_claim hb) hty
  | breakResult =>
      intro Γ Δ hty
      exact (block_bundle_to_claim hb) hty
  | continueResult =>
      intro Γ Δ hty
      exact (block_bundle_to_claim hb) hty
  | returnResult rv =>
      trivial

/-! ### 公開用 normal theorem -/
/--
`normal` 終了した文について、型付け導出と big-step 実行導出が
`StmtControlCompatible` で整合することを述べる公開定理。

意味:
- 内部では導出木に対する相互消去 (`stmt_compat_claim`) を使っている
- 公開側では「normal に型付いた文が normal に実行されたなら、
  その型付けと実行は control 的に食い違わない」という形で使える

役割:
- 以後の preservation 系定理で使う、statement 側の基本 compatibility 定理
- `while` / `break` / `continue` を含む複雑な制御構造も、この定理の中で吸収済み
-/
theorem stmt_normal_control_compatible
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .normalK Γ s Δ)
    (hstep : BigStepStmt σ s .normal σ') :
    StmtControlCompatible hty hstep := by
  simpa using (stmt_compat_claim hstep) hty

/--
`normal` 終了した文ブロックについて、型付け導出と big-step 実行導出が
`BlockControlCompatible` で整合することを述べる公開定理。

意味:
- block 全体が normal に型付いて normal に実行されたなら、
  block の型付けと実行は control 的に整合している
- statement 版の block 対応物

役割:
- block 単位の preservation 系定理に直接つなぐための公開入口
- block 内部の先頭文・残りブロック・制御伝播の整合性をまとめて隠蔽する
-/
theorem block_normal_control_compatible
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .normalK Γ ss Δ)
    (hstep : BigStepBlock σ ss .normal σ') :
    BlockControlCompatible hty hstep := by
  simpa using (block_compat_claim hstep) hty

/--
`normal` に型付いた文が、ready かつ well-scoped / well-typed な具体状態から
`normal` に実行されたとき、実行後状態も結果環境 `Δ` に対して
`ScopedTypedStateConcrete` を満たすことを述べる preservation 定理。

意味:
- statement の normal 実行は、具体状態の scoped typed 性を壊さない
- 始状態が `Γ` に適合し、文がその状態で実行準備済みなら、
  終状態は `Δ` に適合する

役割:
- statement の normal 実行に対する concrete preservation の主定理
- compatibility 定理を preservation 定理へ持ち上げる最初の公開橋
-/
theorem stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep
  exact stmt_control_preserves_scoped_typed_state_of_compatible
    (stmt_normal_control_compatible hty hstep) hσ hready

/--
`normal` に型付いた文ブロックが、ready かつ well-scoped / well-typed な具体状態から
`normal` に実行されたとき、実行後状態も結果環境 `Δ` に対して
`ScopedTypedStateConcrete` を満たすことを述べる preservation 定理。

意味:
- block の normal 実行は、具体状態の scoped typed 性を壊さない
- 始状態が `Γ` に適合し、block がその状態で実行準備済みなら、
  終状態は `Δ` に適合する

役割:
- block の normal 実行に対する concrete preservation の主定理
- statement 版 preservation の block 対応物
-/
theorem block_body_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ →
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    BigStepBlock σ ss .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep
  exact block_control_preserves_scoped_typed_state_of_compatible
    (block_normal_control_compatible hty hstep) hσ hready

/--
`break` に型付いた文について、compatibility 証明が与えられていれば、
`break` 実行後も concrete な scoped typed 性が保存されることを述べる定理。

意味:
- `break` は制御を中断するが、状態の well-scoped / well-typed 性自体は壊さない
- normal 専用ではなく、すでに compatibility が与えられている形で述べている

役割:
- `break` 系の preservation を statement 単位で使うための公開定理
- 上位の loop / block の preservation 証明で利用される
-/
theorem stmt_break_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .breakK Γ s Δ)
    (hstep : BigStepStmt σ s .breakResult σ')
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ hready
  exact stmt_control_preserves_scoped_typed_state_of_compatible hcomp hσ hready

/--
`continue` に型付いた文について、compatibility 証明が与えられていれば、
`continue` 実行後も concrete な scoped typed 性が保存されることを述べる定理。

意味:
- `continue` は loop 本体の残りを飛ばすが、状態整合性は保存される
- 制御チャネルが `continue` であっても preservation は成り立つ

役割:
- loop 本体の `continue` 分岐を扱う preservation の基本部品
-/
theorem stmt_continue_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .continueK Γ s Δ)
    (hstep : BigStepStmt σ s .continueResult σ')
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ hready
  exact stmt_control_preserves_scoped_typed_state_of_compatible hcomp hσ hready

/--
`return` に型付いた文について、compatibility 証明が与えられていれば、
`return` 実行後も concrete な scoped typed 性が保存されることを述べる定理。

意味:
- 関数本体からの脱出であっても、実行後状態の concrete 整合性は保持される
- `rv : Option Value` を持つので、値あり / 値なし return の両方を一括で扱う

役割:
- return 分岐を含む上位 preservation 証明の基本部品
-/
theorem stmt_return_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {rv : Option Value}
    (hty : HasTypeStmtCI .returnK Γ s Δ)
    (hstep : BigStepStmt σ s (.returnResult rv) σ')
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ hready
  exact stmt_control_preserves_scoped_typed_state_of_compatible hcomp hσ hready

/--
`break` に型付いた文ブロックについて、compatibility 証明が与えられていれば、
`break` 実行後も concrete な scoped typed 性が保存されることを述べる定理。

意味:
- block 全体が `break` で終了しても、状態整合性は保たれる
- 先頭文で `break` が起こる場合や途中で伝播する場合を含めて block 単位で扱う

役割:
- loop body や compound statement の `break` 分岐 preservation に使う
-/
theorem block_body_break_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .breakK Γ ss Δ)
    (hstep : BigStepBlock σ ss .breakResult σ')
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ hready
  exact block_control_preserves_scoped_typed_state_of_compatible hcomp hσ hready

/--
`continue` に型付いた文ブロックについて、compatibility 証明が与えられていれば、
`continue` 実行後も concrete な scoped typed 性が保存されることを述べる定理。

意味:
- block 全体が `continue` で終了しても、状態整合性は保たれる
- loop body の内部 block が `continue` を伝播する場合を自然に含む

役割:
- loop 系 preservation の block 版基本部品
-/
theorem block_body_continue_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .continueK Γ ss Δ)
    (hstep : BigStepBlock σ ss .continueResult σ')
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ hready
  exact block_control_preserves_scoped_typed_state_of_compatible hcomp hσ hready

/--
`return` に型付いた文ブロックについて、compatibility 証明が与えられていれば、
`return` 実行後も concrete な scoped typed 性が保存されることを述べる定理。

意味:
- block 全体が関数脱出 (`return`) で終了しても、状態整合性は保たれる
- 値あり / 値なし return の両方を `rv : Option Value` で一括に扱う

役割:
- function body や nested block の return 分岐 preservation の公開定理
-/
theorem block_body_return_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} {rv : Option Value}
    (hty : HasTypeBlockCI .returnK Γ ss Δ)
    (hstep : BigStepBlock σ ss (.returnResult rv) σ')
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ hready
  exact block_control_preserves_scoped_typed_state_of_compatible hcomp hσ hready

end Cpp
