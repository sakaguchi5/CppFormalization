import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Lemmas.ExprDeterminism

namespace Cpp

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

end Cpp
