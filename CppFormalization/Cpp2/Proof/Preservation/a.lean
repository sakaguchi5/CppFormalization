import CppFormalization.Cpp2.Semantics.Expr
import CppFormalization.Cpp2.Typing.Expr
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateBoundary
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

mutual

theorem bigStepPlace_deterministic
    {σ : State} {p : PlaceExpr} {a₁ a₂ : Nat}
    (h₁ : BigStepPlace σ p a₁)
    (h₂ : BigStepPlace σ p a₂) :
    a₁ = a₂ := by
  cases h₁ with
  | varObject hlookup₁ =>
      cases h₂ with
      | varObject hlookup₂ =>
          rw [hlookup₁] at hlookup₂
          cases hlookup₂
          rfl
      | varRef hlookup₂ =>
          rw [hlookup₁] at hlookup₂
          cases hlookup₂
  | varRef hlookup₁ =>
      cases h₂ with
      | varObject hlookup₂ =>
          rw [hlookup₁] at hlookup₂
          cases hlookup₂
      | varRef hlookup₂ =>
          rw [hlookup₁] at hlookup₂
          cases hlookup₂
          rfl
  | deref hval₁ hheap₁ halive₁ =>
      cases h₂ with
      | deref hval₂ hheap₂ halive₂ =>
          have haddr :
              Value.addr a₁ = Value.addr a₂ :=
            bigStepValue_deterministic hval₁ hval₂
          injection haddr with ha

theorem bigStepValue_deterministic
    {σ : State} {e : ValExpr} {v₁ v₂ : Value}
    (h₁ : BigStepValue σ e v₁)
    (h₂ : BigStepValue σ e v₂) :
    v₁ = v₂ := by
  cases h₁ with
  | litBool =>
      cases h₂
      rfl
  | litInt =>
      cases h₂
      rfl
  | load hplace₁ hheap₁ halive₁ hval₁ =>
      cases h₂ with
      | load hplace₂ hheap₂ halive₂ hval₂ =>
          have ha : _ := bigStepPlace_deterministic hplace₁ hplace₂
          subst ha
          rw [hheap₁] at hheap₂
          cases hheap₂
          rw [hval₁] at hval₂
          cases hval₂
          rfl
  | addrOf hplace₁ =>
      cases h₂ with
      | addrOf hplace₂ =>
          have ha : _ := bigStepPlace_deterministic hplace₁ hplace₂
          subst ha
          rfl
  | add h₁₁ h₁₂ =>
      cases h₂ with
      | add h₂₁ h₂₂ =>
          have hv₁ : _ := bigStepValue_deterministic h₁₁ h₂₁
          have hv₂ : _ := bigStepValue_deterministic h₁₂ h₂₂
          injection hv₁ with hn₁
          injection hv₂ with hn₂
          subst hn₁
          subst hn₂
          rfl
  | sub h₁₁ h₁₂ =>
      cases h₂ with
      | sub h₂₁ h₂₂ =>
          have hv₁ : _ := bigStepValue_deterministic h₁₁ h₂₁
          have hv₂ : _ := bigStepValue_deterministic h₁₂ h₂₂
          injection hv₁ with hn₁
          injection hv₂ with hn₂
          subst hn₁
          subst hn₂
          rfl
  | mul h₁₁ h₁₂ =>
      cases h₂ with
      | mul h₂₁ h₂₂ =>
          have hv₁ : _ := bigStepValue_deterministic h₁₁ h₂₁
          have hv₂ : _ := bigStepValue_deterministic h₁₂ h₂₂
          injection hv₁ with hn₁
          injection hv₂ with hn₂
          subst hn₁
          subst hn₂
          rfl
  | eq h₁₁ h₁₂ =>
      cases h₂ with
      | eq h₂₁ h₂₂ =>
          have hv₁ : _ := bigStepValue_deterministic h₁₁ h₂₁
          have hv₂ : _ := bigStepValue_deterministic h₁₂ h₂₂
          simp [hv₁, hv₂]
  | lt h₁₁ h₁₂ =>
      cases h₂ with
      | lt h₂₁ h₂₂ =>
          have hv₁ : _ := bigStepValue_deterministic h₁₁ h₂₁
          have hv₂ : _ := bigStepValue_deterministic h₁₂ h₂₂
          injection hv₁ with hn₁
          injection hv₂ with hn₂
          subst hn₁
          subst hn₂
          rfl
  | not h₁ =>
      cases h₂ with
      | not h₂ =>
          have hv : _ := bigStepValue_deterministic h₁ h₂
          injection hv with hb
          subst hb
          rfl

end

theorem expr_ready_eval_compat'
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {v : Value}
    (hre : ExprReadyConcrete Γ σ e τ)
    (hstep : BigStepValue σ e v) :
    ValueCompat v τ := by
  cases hre with
  | litBool =>
      cases hstep
      exact ValueCompat.bool
  | litInt =>
      cases hstep
      exact ValueCompat.int
  | load hp hread =>
      cases hstep with
      | load hplace hheap halive hval =>
          rcases hread with ⟨a₀, hplace₀, c₀, v₀, hheap₀, hty₀, halive₀, hval₀, hcompat₀⟩
          have ha : a₀ = _ := bigStepPlace_deterministic hplace₀ hplace
          subst ha
          rw [hheap₀] at hheap
          cases hheap
          rw [hval₀] at hval
          cases hval
          simpa [hty₀] using hcompat₀
  | addrOf hp =>
      cases hstep with
      | addrOf hplace =>
          exact ValueCompat.ptr
  | add h₁ h₂ =>
      cases hstep
      exact ValueCompat.int
  | sub h₁ h₂ =>
      cases hstep
      exact ValueCompat.int
  | mul h₁ h₂ =>
      cases hstep
      exact ValueCompat.int
  | eq h₁ h₂ =>
      cases hstep
      exact ValueCompat.bool
  | lt h₁ h₂ =>
      cases hstep
      exact ValueCompat.bool
  | not h =>
      cases hstep
      exact ValueCompat.bool

theorem expr_ready_eval_compat
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {v : Value}
    (hre : ExprReadyConcrete Γ σ e τ)
    (hstep : BigStepValue σ e v) :
    ValueCompat v τ := by
  exact expr_ready_eval_compat' hre hstep


/--
  状態が整合しており、場所 p が型 τ で Ready ならば、
  そこから load した値 v は必ず型 τ と互換である
-/
theorem load_preserves_compat
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} {v : Value}
    (hre : ExprReadyConcrete Γ σ (ValExpr.load p) τ)
    (hstep : BigStepValue σ (ValExpr.load p) v) :
    ValueCompat v τ := by
  -- 1. hready と hstep を分解する
  cases hre with
  | load hrp hread_info =>
    rcases hread_info with ⟨a_ready, hplace_ready, hreadable⟩
    cases hstep with
    | load hplace hheap halive hval =>
      -- 2. 決定性補題を使い、アドレスが同一であることを示す
      -- (BigStepPlace σ p a_ready と BigStepPlace σ p a)
      have heq_a : a_ready = _ := bigStepPlace_deterministic hplace_ready hplace
      subst heq_a

      -- 3. CellReadableTyped の定義を分解して ValueCompat を取り出す
      rcases hreadable with ⟨c_ready, v_ready, hheap_ready, hty_ready, halive_ready, hval_ready, hcompat⟩

      -- 4. 同じアドレス a の heap にある Cell は一意
      rw [hheap_ready] at hheap
      cases hheap -- c_ready = c

      -- 5. 同じ Cell の中にある value も一意
      rw [hval_ready] at hval
      cases hval -- v_ready = v

      -- 6. 結論
      exact hcompat

mutual

theorem expr_ready_to_bigstep
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
    (hre : ExprReadyConcrete Γ σ e τ) :
    ∃ v, BigStepValue σ e v := by
  match hre with
  | .litBool (b := b) =>
      exists (Value.bool b)
      apply BigStepValue.litBool
  | .litInt (n := n) =>
      exists (Value.int n)
      apply BigStepValue.litInt
  | .load hrp hinfo =>
      rcases hinfo with ⟨a, hplace, hreadable⟩
      rcases hreadable with ⟨c, v, hheap, hty, halive, hval, hcompat⟩
      exists v
      apply BigStepValue.load hplace hheap halive hval
  | .addrOf hrp =>
      let ⟨a, hp⟩ := place_ready_to_bigstep hrp
      exists (Value.addr a)
      apply BigStepValue.addrOf hp
  | .add h1 h2 =>
      let ⟨v1, hv1⟩ := expr_ready_to_bigstep h1
      let ⟨v2, hv2⟩ := expr_ready_to_bigstep h2
      cases expr_ready_eval_compat' h1 hv1
      cases expr_ready_eval_compat' h2 hv2
      refine ⟨_, BigStepValue.add hv1 hv2⟩
  | .sub h1 h2 =>
      let ⟨v1, hv1⟩ := expr_ready_to_bigstep h1
      let ⟨v2, hv2⟩ := expr_ready_to_bigstep h2
      cases expr_ready_eval_compat' h1 hv1
      cases expr_ready_eval_compat' h2 hv2
      refine ⟨_, BigStepValue.sub hv1 hv2⟩
  | .mul h1 h2 =>
      let ⟨v1, hv1⟩ := expr_ready_to_bigstep h1
      let ⟨v2, hv2⟩ := expr_ready_to_bigstep h2
      cases expr_ready_eval_compat' h1 hv1
      cases expr_ready_eval_compat' h2 hv2
      refine ⟨_, BigStepValue.mul hv1 hv2⟩

  | .eq h1 h2 =>
      let ⟨v1, hv1⟩ := expr_ready_to_bigstep h1
      let ⟨v2, hv2⟩ := expr_ready_to_bigstep h2
      exists (Value.bool (decide (v1 = v2)))
      apply BigStepValue.eq hv1 hv2

  | .lt h1 h2 =>
    let ⟨v1, hv1⟩ := expr_ready_to_bigstep h1
    let ⟨v2, hv2⟩ := expr_ready_to_bigstep h2
    cases expr_ready_eval_compat' h1 hv1
    cases expr_ready_eval_compat' h2 hv2
    refine ⟨_, BigStepValue.lt hv1 hv2⟩

  | .not h =>
    let ⟨v, hv⟩ := expr_ready_to_bigstep h
    cases expr_ready_eval_compat' h hv
    refine ⟨_, BigStepValue.not hv⟩

/-- Ready な場所式 (PlaceExpr) は必ず特定のアドレス a に評価される -/
theorem place_ready_to_bigstep
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType}
    (hrp : PlaceReadyConcrete Γ σ p τ) :
    ∃ a, BigStepPlace σ p a := by
  match hrp with
  | .varObject (a := a) _ hbinding _ =>
      exists a
      apply BigStepPlace.varObject hbinding
  | .varRef (a := a) _ hbinding _ =>
      exists a
      apply BigStepPlace.varRef hbinding
  | .deref (e := e) (a := a) hptr hlive =>
      let ⟨_, hstep_e⟩ := hptr
      rcases hlive with ⟨c, hlookup, hty, halive_proof⟩
      exists a
      apply BigStepPlace.deref hstep_e hlookup halive_proof


end


--CellReadableTyped の分解アクセサ
theorem cell_readable_to_compat
    {σ a τ c v}
    (hread : CellReadableTyped σ a τ)
    (hheap : σ.heap a = some c)
    (hval : c.value = some v) :
    ValueCompat v τ := by
  rcases hread with ⟨c', v', hheap', hty', halive', hval', hcompat⟩
  rw [hheap'] at hheap; cases hheap
  rw [hval'] at hval; cases hval
  exact hcompat

theorem assigns_deterministic {σ p v σ₁ σ₂} (h₁ : Assigns σ p v σ₁) (h₂ : Assigns σ p v σ₂) : σ₁ = σ₂ := by
  rcases h₁ with ⟨a₁, c₁, hp₁, hh₁, ha₁, hvt₁, hs₁⟩
  rcases h₂ with ⟨a₂, c₂, hp₂, hh₂, ha₂, hvt₂, hs₂⟩
  have haeq : a₁ = a₂ := bigStepPlace_deterministic hp₁ hp₂
  subst haeq
  rw [hh₁] at hh₂; cases hh₂
  exact hs₁.trans hs₂.symm


-- aNext が同じなら、オブジェクト宣言後の状態は一意
theorem declaresObjectWithNext_deterministic {σ τ x ov aNext σ₁ σ₂}
    (h₁ : DeclaresObjectWithNext σ τ x ov aNext σ₁)
    (h₂ : DeclaresObjectWithNext σ τ x ov aNext σ₂) : σ₁ = σ₂ := by
  rcases h₁ with ⟨_, _, _, _, hs₁⟩
  rcases h₂ with ⟨_, _, _, _, hs₂⟩
  exact hs₁.trans hs₂.symm

-- スコープ操作の一意性
theorem openScope_deterministic {σ σ₁ σ₂}
    (h₁ : OpenScope σ σ₁) (h₂ : OpenScope σ σ₂) : σ₁ = σ₂ :=
  h₁.trans h₂.symm

theorem closeScope_deterministic {σ σ₁ σ₂}
    (h₁ : CloseScope σ σ₁) (h₂ : CloseScope σ σ₂) : σ₁ = σ₂ := by
  cases h₁.symm.trans h₂
  rfl


theorem declaresRef_deterministic {σ τ x a σ₁ σ₂} (h₁ : DeclaresRef σ τ x a σ₁) (h₂ : DeclaresRef σ τ x a σ₂) : σ₁ = σ₂ := by
  rcases h₁ with ⟨_, _, hh₁, _, _, hs₁⟩
  rcases h₂ with ⟨_, _, hh₂, _, _, hs₂⟩
  exact hs₁.trans hs₂.symm


-- CtrlResult の引数として .normal を追加します
theorem exprStmt_deterministic {σ e σ₁ σ₂}
    (h₁ : BigStepStmt σ (.exprStmt e) .normal σ₁)
    (h₂ : BigStepStmt σ (.exprStmt e) .normal σ₂) : σ₁ = σ₂ := by
  cases h₁
  cases h₂
  rfl


mutual

inductive NoDeclareObjStmt : CppStmt → Prop where
  | skip :
      NoDeclareObjStmt .skip
  | exprStmt {e : ValExpr} :
      NoDeclareObjStmt (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} :
      NoDeclareObjStmt (.assign p e)
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} :
      NoDeclareObjStmt (.declareRef τ x p)
  | seq {s t : CppStmt} :
      NoDeclareObjStmt s →
      NoDeclareObjStmt t →
      NoDeclareObjStmt (.seq s t)
  | ite {c : ValExpr} {s t : CppStmt} :
      NoDeclareObjStmt s →
      NoDeclareObjStmt t →
      NoDeclareObjStmt (.ite c s t)
  | whileStmt {c : ValExpr} {body : CppStmt} :
      NoDeclareObjStmt body →
      NoDeclareObjStmt (.whileStmt c body)
  | block {ss : StmtBlock} :
      NoDeclareObjBlock ss →
      NoDeclareObjStmt (.block ss)
  | breakStmt :
      NoDeclareObjStmt .breakStmt
  | continueStmt :
      NoDeclareObjStmt .continueStmt
  | returnStmt {oe : Option ValExpr} :
      NoDeclareObjStmt (.returnStmt oe)

inductive NoDeclareObjBlock : StmtBlock → Prop where
  | nil :
      NoDeclareObjBlock .nil
  | cons {s : CppStmt} {ss : StmtBlock} :
      NoDeclareObjStmt s →
      NoDeclareObjBlock ss →
      NoDeclareObjBlock (.cons s ss)

end

mutual

theorem bigStepStmt_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {ctrl₁ ctrl₂ : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s ctrl₁ σ₁)
    (h₂ : BigStepStmt σ s ctrl₂ σ₂) :
    ctrl₁ = ctrl₂ ∧ σ₁ = σ₂ := by
  match h₁ with
  | .skip =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .expr hv₁ =>
      cases h₂ with
      | expr hv₂ =>
          have _ := bigStepValue_deterministic hv₁ hv₂
          exact ⟨rfl, rfl⟩

  | .assign hv₁ ha₁ =>
      cases h₂ with
      | assign hv₂ ha₂ =>
          have hv : _ := bigStepValue_deterministic hv₁ hv₂
          subst hv
          exact ⟨rfl, assigns_deterministic ha₁ ha₂⟩

  | .declareObjNone _ =>
      cases hno

  | .declareObjSome _ _ =>
      cases hno

  | .declareRef hp₁ hr₁ =>
      cases h₂ with
      | declareRef hp₂ hr₂ =>
          have hp : _ := bigStepPlace_deterministic hp₁ hp₂
          subst hp
          exact ⟨rfl, declaresRef_deterministic hr₁ hr₂⟩

  | .seqNormal hs₁ ht₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              subst hσS
              rcases bigStepStmt_deterministic_noDeclareObj hnoT ht₁ ht₂ with ⟨hcT, hσT⟩
              exact ⟨hcT, hσT⟩
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS

  | .seqBreak hs₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              exact ⟨rfl, hσS⟩
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS

  | .seqContinue hs₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              exact ⟨rfl, hσS⟩
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS

  | .seqReturn hs₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              exact ⟨rfl, hσS⟩

  | .iteTrue hv₁ hs₁ =>
      cases hno with
      | ite hnoS hnoT =>
          cases h₂ with
          | iteTrue hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hctrl, hσ⟩
              exact ⟨hctrl, hσ⟩
          | iteFalse hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc

  | .iteFalse hv₁ hs₁ =>
      cases hno with
      | ite hnoS hnoT =>
          cases h₂ with
          | iteTrue hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | iteFalse hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoT hs₁ hs₂ with ⟨hctrl, hσ⟩
              exact ⟨hctrl, hσ⟩

  | .whileFalse hv₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              exact ⟨rfl, rfl⟩
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc

  | .whileTrueNormal hv₁ hb₁ hw₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              subst hσb
              rcases bigStepStmt_deterministic_noDeclareObj (.whileStmt hnoBody) hw₁ hw₂ with ⟨hcw, hσw⟩
              exact ⟨hcw, hσw⟩
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb

  | .whileTrueBreak hv₁ hb₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              exact ⟨rfl, hσb⟩
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb

  | .whileTrueContinue hv₁ hb₁ hw₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              subst hσb
              rcases bigStepStmt_deterministic_noDeclareObj (.whileStmt hnoBody) hw₁ hw₂ with ⟨hcw, hσw⟩
              exact ⟨hcw, hσw⟩
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb

  | .whileTrueReturn hv₁ hb₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              exact ⟨rfl, hσb⟩

  | .block ho₁ hb₁ hc₁ =>
      cases hno with
      | block hnoB =>
          cases h₂ with
          | block ho₂ hb₂ hc₂ =>
              have hOpen : _ := openScope_deterministic ho₁ ho₂
              subst hOpen
              rcases bigStepBlock_deterministic_noDeclareObj hnoB hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              subst hσb
              exact ⟨rfl, closeScope_deterministic hc₁ hc₂⟩

  | .breakStmt =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .continueStmt =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .returnNoneStmt =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .returnSome hv₁ =>
      cases h₂ with
      | returnSome hv₂ =>
          have hv : _ := bigStepValue_deterministic hv₁ hv₂
          subst hv
          exact ⟨rfl, rfl⟩

theorem bigStepBlock_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {ctrl₁ ctrl₂ : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss ctrl₁ σ₁)
    (h₂ : BigStepBlock σ ss ctrl₂ σ₂) :
    ctrl₁ = ctrl₂ ∧ σ₁ = σ₂ := by
  match h₁ with
  | .nil =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .consNormal hs₁ hb₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              subst hσs
              rcases bigStepBlock_deterministic_noDeclareObj hnoB hb₁ hb₂ with ⟨hcb, hσb⟩
              exact ⟨hcb, hσb⟩
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs

  | .consBreak hs₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              exact ⟨rfl, hσs⟩
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs

  | .consContinue hs₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              exact ⟨rfl, hσs⟩
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs

  | .consReturn hs₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              exact ⟨rfl, hσs⟩

end

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
