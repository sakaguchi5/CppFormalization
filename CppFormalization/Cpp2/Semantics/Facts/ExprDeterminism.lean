import CppFormalization.Cpp2.Semantics.Expr

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
end Cpp
