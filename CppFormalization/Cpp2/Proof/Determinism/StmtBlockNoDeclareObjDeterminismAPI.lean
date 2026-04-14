import CppFormalization.Cpp2.Proof.Determinism.StmtBlockNoDeclareObjDeterminismCore

namespace Cpp

theorem bigStepStmt_state_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s ctrl σ₁)
    (h₂ : BigStepStmt σ s ctrl σ₂) :
    σ₁ = σ₂ := by
  rcases bigStepStmt_deterministic_noDeclareObj hno h₁ h₂ with ⟨_, hσ⟩
  exact hσ

theorem bigStepBlock_state_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss ctrl σ₁)
    (h₂ : BigStepBlock σ ss ctrl σ₂) :
    σ₁ = σ₂ := by
  rcases bigStepBlock_deterministic_noDeclareObj hno h₁ h₂ with ⟨_, hσ⟩
  exact hσ



@[simp] theorem noDeclareObjStmt_skip_iff :
    NoDeclareObjStmt .skip ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .skip

@[simp] theorem noDeclareObjStmt_exprStmt_iff {e : ValExpr} :
    NoDeclareObjStmt (.exprStmt e) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .exprStmt

@[simp] theorem noDeclareObjStmt_assign_iff {p : PlaceExpr} {e : ValExpr} :
    NoDeclareObjStmt (.assign p e) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .assign

@[simp] theorem noDeclareObjStmt_declareObj_iff
    {τ : CppType} {x : Ident} {oe : Option ValExpr} :
    NoDeclareObjStmt (.declareObj τ x oe) ↔ False := by
  constructor
  · intro h
    cases h
  · intro h
    cases h

@[simp] theorem noDeclareObjStmt_declareRef_iff
    {τ : CppType} {x : Ident} {p : PlaceExpr} :
    NoDeclareObjStmt (.declareRef τ x p) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .declareRef

@[simp] theorem noDeclareObjStmt_seq_iff
    {s t : CppStmt} :
    NoDeclareObjStmt (.seq s t) ↔
      NoDeclareObjStmt s ∧ NoDeclareObjStmt t := by
  constructor
  · intro h
    cases h with
    | seq hs ht =>
        exact ⟨hs, ht⟩
  · rintro ⟨hs, ht⟩
    exact .seq hs ht

@[simp] theorem noDeclareObjStmt_ite_iff
    {c : ValExpr} {s t : CppStmt} :
    NoDeclareObjStmt (.ite c s t) ↔
      NoDeclareObjStmt s ∧ NoDeclareObjStmt t := by
  constructor
  · intro h
    cases h with
    | ite hs ht =>
        exact ⟨hs, ht⟩
  · rintro ⟨hs, ht⟩
    exact .ite hs ht

@[simp] theorem noDeclareObjStmt_whileStmt_iff
    {c : ValExpr} {body : CppStmt} :
    NoDeclareObjStmt (.whileStmt c body) ↔ NoDeclareObjStmt body := by
  constructor
  · intro h
    cases h with
    | whileStmt hbody =>
        exact hbody
  · intro hbody
    exact .whileStmt hbody

@[simp] theorem noDeclareObjStmt_block_iff
    {ss : StmtBlock} :
    NoDeclareObjStmt (.block ss) ↔ NoDeclareObjBlock ss := by
  constructor
  · intro h
    cases h with
    | block hss =>
        exact hss
  · intro hss
    exact .block hss

@[simp] theorem noDeclareObjStmt_breakStmt_iff :
    NoDeclareObjStmt .breakStmt ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .breakStmt

@[simp] theorem noDeclareObjStmt_continueStmt_iff :
    NoDeclareObjStmt .continueStmt ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .continueStmt

@[simp] theorem noDeclareObjStmt_returnStmt_iff
    {oe : Option ValExpr} :
    NoDeclareObjStmt (.returnStmt oe) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .returnStmt

@[simp] theorem noDeclareObjBlock_nil_iff :
    NoDeclareObjBlock .nil ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .nil

@[simp] theorem noDeclareObjBlock_cons_iff
    {s : CppStmt} {ss : StmtBlock} :
    NoDeclareObjBlock (.cons s ss) ↔
      NoDeclareObjStmt s ∧ NoDeclareObjBlock ss := by
  constructor
  · intro h
    cases h with
    | cons hs hss =>
        exact ⟨hs, hss⟩
  · rintro ⟨hs, hss⟩
    exact .cons hs hss

theorem NoDeclareObjStmt.seq_left
    {s t : CppStmt}
    (h : NoDeclareObjStmt (.seq s t)) :
    NoDeclareObjStmt s := by
  exact (noDeclareObjStmt_seq_iff.mp h).1

theorem NoDeclareObjStmt.seq_right
    {s t : CppStmt}
    (h : NoDeclareObjStmt (.seq s t)) :
    NoDeclareObjStmt t := by
  exact (noDeclareObjStmt_seq_iff.mp h).2

theorem NoDeclareObjStmt.ite_then
    {c : ValExpr} {s t : CppStmt}
    (h : NoDeclareObjStmt (.ite c s t)) :
    NoDeclareObjStmt s := by
  exact (noDeclareObjStmt_ite_iff.mp h).1

theorem NoDeclareObjStmt.ite_else
    {c : ValExpr} {s t : CppStmt}
    (h : NoDeclareObjStmt (.ite c s t)) :
    NoDeclareObjStmt t := by
  exact (noDeclareObjStmt_ite_iff.mp h).2

theorem NoDeclareObjStmt.while_body
    {c : ValExpr} {body : CppStmt}
    (h : NoDeclareObjStmt (.whileStmt c body)) :
    NoDeclareObjStmt body := by
  exact noDeclareObjStmt_whileStmt_iff.mp h

theorem NoDeclareObjStmt.block_body
    {ss : StmtBlock}
    (h : NoDeclareObjStmt (.block ss)) :
    NoDeclareObjBlock ss := by
  exact noDeclareObjStmt_block_iff.mp h

theorem NoDeclareObjBlock.cons_head
    {s : CppStmt} {ss : StmtBlock}
    (h : NoDeclareObjBlock (.cons s ss)) :
    NoDeclareObjStmt s := by
  exact (noDeclareObjBlock_cons_iff.mp h).1

theorem NoDeclareObjBlock.cons_tail
    {s : CppStmt} {ss : StmtBlock}
    (h : NoDeclareObjBlock (.cons s ss)) :
    NoDeclareObjBlock ss := by
  exact (noDeclareObjBlock_cons_iff.mp h).2



mutual

def decNoDeclareObjStmt : (s : CppStmt) → Decidable (NoDeclareObjStmt s)
  | .skip =>
      isTrue NoDeclareObjStmt.skip
  | .exprStmt _ =>
      isTrue NoDeclareObjStmt.exprStmt
  | .assign _ _ =>
      isTrue NoDeclareObjStmt.assign
  | .declareObj _ _ _ =>
      isFalse (by
        intro h
        simp at h)
  | .declareRef _ _ _ =>
      isTrue NoDeclareObjStmt.declareRef
  | .seq s t =>
      match decNoDeclareObjStmt s, decNoDeclareObjStmt t with
      | isTrue hs, isTrue ht =>
          isTrue (NoDeclareObjStmt.seq hs ht)
      | isFalse hs, _ =>
          isFalse (by
            intro h
            exact hs (NoDeclareObjStmt.seq_left h))
      | _, isFalse ht =>
          isFalse (by
            intro h
            exact ht (NoDeclareObjStmt.seq_right h))
  | .ite _ s t =>
      match decNoDeclareObjStmt s, decNoDeclareObjStmt t with
      | isTrue hs, isTrue ht =>
          isTrue (NoDeclareObjStmt.ite hs ht)
      | isFalse hs, _ =>
          isFalse (by
            intro h
            exact hs (NoDeclareObjStmt.ite_then h))
      | _, isFalse ht =>
          isFalse (by
            intro h
            exact ht (NoDeclareObjStmt.ite_else h))
  | .whileStmt _ body =>
      match decNoDeclareObjStmt body with
      | isTrue hbody =>
          isTrue (NoDeclareObjStmt.whileStmt hbody)
      | isFalse hbody =>
          isFalse (by
            intro h
            exact hbody (NoDeclareObjStmt.while_body h))
  | .block ss =>
      match decNoDeclareObjBlock ss with
      | isTrue hss =>
          isTrue (NoDeclareObjStmt.block hss)
      | isFalse hss =>
          isFalse (by
            intro h
            exact hss (NoDeclareObjStmt.block_body h))
  | .breakStmt =>
      isTrue NoDeclareObjStmt.breakStmt
  | .continueStmt =>
      isTrue NoDeclareObjStmt.continueStmt
  | .returnStmt _ =>
      isTrue NoDeclareObjStmt.returnStmt

def decNoDeclareObjBlock : (ss : StmtBlock) → Decidable (NoDeclareObjBlock ss)
  | .nil =>
      isTrue NoDeclareObjBlock.nil
  | .cons s ss =>
      match decNoDeclareObjStmt s, decNoDeclareObjBlock ss with
      | isTrue hs, isTrue hss =>
          isTrue (NoDeclareObjBlock.cons hs hss)
      | isFalse hs, _ =>
          isFalse (by
            intro h
            exact hs (NoDeclareObjBlock.cons_head h))
      | _, isFalse hss =>
          isFalse (by
            intro h
            exact hss (NoDeclareObjBlock.cons_tail h))

end

instance instDecidableNoDeclareObjStmt (s : CppStmt) :
    Decidable (NoDeclareObjStmt s) :=
  decNoDeclareObjStmt s

instance instDecidableNoDeclareObjBlock (ss : StmtBlock) :
    Decidable (NoDeclareObjBlock ss) :=
  decNoDeclareObjBlock ss




theorem bigStepStmt_normal_state_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s CtrlResult.normal σ₁)
    (h₂ : BigStepStmt σ s CtrlResult.normal σ₂) :
    σ₁ = σ₂ := by
  exact bigStepStmt_state_deterministic_noDeclareObj hno h₁ h₂

theorem bigStepStmt_break_state_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s CtrlResult.breakResult σ₁)
    (h₂ : BigStepStmt σ s CtrlResult.breakResult σ₂) :
    σ₁ = σ₂ := by
  exact bigStepStmt_state_deterministic_noDeclareObj hno h₁ h₂

theorem bigStepStmt_continue_state_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s CtrlResult.continueResult σ₁)
    (h₂ : BigStepStmt σ s CtrlResult.continueResult σ₂) :
    σ₁ = σ₂ := by
  exact bigStepStmt_state_deterministic_noDeclareObj hno h₁ h₂

theorem bigStepStmt_return_state_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s (CtrlResult.returnResult rv) σ₁)
    (h₂ : BigStepStmt σ s (CtrlResult.returnResult rv) σ₂) :
    σ₁ = σ₂ := by
  exact bigStepStmt_state_deterministic_noDeclareObj hno h₁ h₂

theorem bigStepBlock_normal_state_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss CtrlResult.normal σ₁)
    (h₂ : BigStepBlock σ ss CtrlResult.normal σ₂) :
    σ₁ = σ₂ := by
  exact bigStepBlock_state_deterministic_noDeclareObj hno h₁ h₂

theorem bigStepBlock_break_state_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss CtrlResult.breakResult σ₁)
    (h₂ : BigStepBlock σ ss CtrlResult.breakResult σ₂) :
    σ₁ = σ₂ := by
  exact bigStepBlock_state_deterministic_noDeclareObj hno h₁ h₂

theorem bigStepBlock_continue_state_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss CtrlResult.continueResult σ₁)
    (h₂ : BigStepBlock σ ss CtrlResult.continueResult σ₂) :
    σ₁ = σ₂ := by
  exact bigStepBlock_state_deterministic_noDeclareObj hno h₁ h₂

theorem bigStepBlock_return_state_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss (CtrlResult.returnResult rv) σ₁)
    (h₂ : BigStepBlock σ ss (CtrlResult.returnResult rv) σ₂) :
    σ₁ = σ₂ := by
  exact bigStepBlock_state_deterministic_noDeclareObj hno h₁ h₂



theorem bigStepStmt_ctrl_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {ctrl₁ ctrl₂ : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s ctrl₁ σ₁)
    (h₂ : BigStepStmt σ s ctrl₂ σ₂) :
    ctrl₁ = ctrl₂ := by
  exact (bigStepStmt_deterministic_noDeclareObj hno h₁ h₂).1

theorem bigStepBlock_ctrl_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {ctrl₁ ctrl₂ : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss ctrl₁ σ₁)
    (h₂ : BigStepBlock σ ss ctrl₂ σ₂) :
    ctrl₁ = ctrl₂ := by
  exact (bigStepBlock_deterministic_noDeclareObj hno h₁ h₂).1

theorem bigStepStmt_not_normal_and_break_noDeclareObj
    {σ : State} {s : CppStmt} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (hn : BigStepStmt σ s CtrlResult.normal σ₁)
    (hb : BigStepStmt σ s CtrlResult.breakResult σ₂) :
    False := by
  have hctrl :=
    bigStepStmt_ctrl_deterministic_noDeclareObj hno hn hb
  cases hctrl

theorem bigStepStmt_not_normal_and_continue_noDeclareObj
    {σ : State} {s : CppStmt} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (hn : BigStepStmt σ s CtrlResult.normal σ₁)
    (hc : BigStepStmt σ s CtrlResult.continueResult σ₂) :
    False := by
  have hctrl :=
    bigStepStmt_ctrl_deterministic_noDeclareObj hno hn hc
  cases hctrl

theorem bigStepStmt_not_break_and_continue_noDeclareObj
    {σ : State} {s : CppStmt} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (hb : BigStepStmt σ s CtrlResult.breakResult σ₁)
    (hc : BigStepStmt σ s CtrlResult.continueResult σ₂) :
    False := by
  have hctrl :=
    bigStepStmt_ctrl_deterministic_noDeclareObj hno hb hc
  cases hctrl

theorem bigStepStmt_not_normal_and_return_noDeclareObj
    {σ : State} {s : CppStmt} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (hn : BigStepStmt σ s CtrlResult.normal σ₁)
    (hr : BigStepStmt σ s (CtrlResult.returnResult rv) σ₂) :
    False := by
  have hctrl :=
    bigStepStmt_ctrl_deterministic_noDeclareObj hno hn hr
  cases hctrl

theorem bigStepBlock_not_normal_and_break_noDeclareObj
    {σ : State} {ss : StmtBlock} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (hn : BigStepBlock σ ss CtrlResult.normal σ₁)
    (hb : BigStepBlock σ ss CtrlResult.breakResult σ₂) :
    False := by
  have hctrl :=
    bigStepBlock_ctrl_deterministic_noDeclareObj hno hn hb
  cases hctrl


theorem bigStepStmt_not_break_and_return_noDeclareObj
    {σ : State} {s : CppStmt} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (hb : BigStepStmt σ s CtrlResult.breakResult σ₁)
    (hr : BigStepStmt σ s (CtrlResult.returnResult rv) σ₂) :
    False := by
  have hctrl :=
    bigStepStmt_ctrl_deterministic_noDeclareObj hno hb hr
  cases hctrl

theorem bigStepStmt_not_continue_and_return_noDeclareObj
    {σ : State} {s : CppStmt} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (hc : BigStepStmt σ s CtrlResult.continueResult σ₁)
    (hr : BigStepStmt σ s (CtrlResult.returnResult rv) σ₂) :
    False := by
  have hctrl :=
    bigStepStmt_ctrl_deterministic_noDeclareObj hno hc hr
  cases hctrl

theorem bigStepBlock_not_normal_and_continue_noDeclareObj
    {σ : State} {ss : StmtBlock} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (hn : BigStepBlock σ ss CtrlResult.normal σ₁)
    (hc : BigStepBlock σ ss CtrlResult.continueResult σ₂) :
    False := by
  have hctrl :=
    bigStepBlock_ctrl_deterministic_noDeclareObj hno hn hc
  cases hctrl

theorem bigStepBlock_not_normal_and_return_noDeclareObj
    {σ : State} {ss : StmtBlock} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (hn : BigStepBlock σ ss CtrlResult.normal σ₁)
    (hr : BigStepBlock σ ss (CtrlResult.returnResult rv) σ₂) :
    False := by
  have hctrl :=
    bigStepBlock_ctrl_deterministic_noDeclareObj hno hn hr
  cases hctrl

theorem bigStepBlock_not_break_and_continue_noDeclareObj
    {σ : State} {ss : StmtBlock} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (hb : BigStepBlock σ ss CtrlResult.breakResult σ₁)
    (hc : BigStepBlock σ ss CtrlResult.continueResult σ₂) :
    False := by
  have hctrl :=
    bigStepBlock_ctrl_deterministic_noDeclareObj hno hb hc
  cases hctrl

theorem bigStepBlock_not_break_and_return_noDeclareObj
    {σ : State} {ss : StmtBlock} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (hb : BigStepBlock σ ss CtrlResult.breakResult σ₁)
    (hr : BigStepBlock σ ss (CtrlResult.returnResult rv) σ₂) :
    False := by
  have hctrl :=
    bigStepBlock_ctrl_deterministic_noDeclareObj hno hb hr
  cases hctrl

theorem bigStepBlock_not_continue_and_return_noDeclareObj
    {σ : State} {ss : StmtBlock} {rv : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (hc : BigStepBlock σ ss CtrlResult.continueResult σ₁)
    (hr : BigStepBlock σ ss (CtrlResult.returnResult rv) σ₂) :
    False := by
  have hctrl :=
    bigStepBlock_ctrl_deterministic_noDeclareObj hno hc hr
  cases hctrl

theorem bigStepStmt_return_value_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {rv₁ rv₂ : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s (CtrlResult.returnResult rv₁) σ₁)
    (h₂ : BigStepStmt σ s (CtrlResult.returnResult rv₂) σ₂) :
    rv₁ = rv₂ := by
  have hctrl :=
    bigStepStmt_ctrl_deterministic_noDeclareObj hno h₁ h₂
  cases hctrl
  rfl

theorem bigStepBlock_return_value_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {rv₁ rv₂ : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss (CtrlResult.returnResult rv₁) σ₁)
    (h₂ : BigStepBlock σ ss (CtrlResult.returnResult rv₂) σ₂) :
    rv₁ = rv₂ := by
  have hctrl :=
    bigStepBlock_ctrl_deterministic_noDeclareObj hno h₁ h₂
  cases hctrl
  rfl

theorem bigStepStmt_return_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {rv₁ rv₂ : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s (CtrlResult.returnResult rv₁) σ₁)
    (h₂ : BigStepStmt σ s (CtrlResult.returnResult rv₂) σ₂) :
    rv₁ = rv₂ ∧ σ₁ = σ₂ := by
  have hdet := bigStepStmt_deterministic_noDeclareObj hno h₁ h₂
  rcases hdet with ⟨hctrl, hσ⟩
  cases hctrl
  exact ⟨rfl, hσ⟩

theorem bigStepBlock_return_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {rv₁ rv₂ : Option Value} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss (CtrlResult.returnResult rv₁) σ₁)
    (h₂ : BigStepBlock σ ss (CtrlResult.returnResult rv₂) σ₂) :
    rv₁ = rv₂ ∧ σ₁ = σ₂ := by
  have hdet := bigStepBlock_deterministic_noDeclareObj hno h₁ h₂
  rcases hdet with ⟨hctrl, hσ⟩
  cases hctrl
  exact ⟨rfl, hσ⟩

end Cpp
