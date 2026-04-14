import CppFormalization.Cpp2.Typing.Expr

namespace Cpp

mutual

theorem hasPlaceType_unique
    {Γ : TypeEnv} {p : PlaceExpr} {τ₁ τ₂ : CppType}
    (h₁ : HasPlaceType Γ p τ₁)
    (h₂ : HasPlaceType Γ p τ₂) :
    τ₁ = τ₂ := by
  cases h₁ with
  | var hlookup =>
      rename_i x d
      cases h₂ with
      | var hlookup' =>
          rename_i d'
          rw [hlookup] at hlookup'
          cases hlookup'
          rfl
  | deref hv =>
      rename_i e
      cases h₂ with
      | deref hv' =>
          have hptr : CppType.ptr τ₁ = CppType.ptr τ₂ :=
            hasValueType_unique hv hv'
          injection hptr with hτ

theorem hasValueType_unique
    {Γ : TypeEnv} {e : ValExpr} {τ₁ τ₂ : CppType}
    (h₁ : HasValueType Γ e τ₁)
    (h₂ : HasValueType Γ e τ₂) :
    τ₁ = τ₂ := by
  cases h₁ with
  | litBool =>
      cases h₂ <;> rfl
  | litInt =>
      cases h₂ <;> rfl
  | load hp =>
      rename_i p
      cases h₂ with
      | load hp' =>
          exact hasPlaceType_unique hp hp'
  | addrOf hp =>
      rename_i p τ
      cases h₂ with
      | addrOf hp' =>
          rename_i τ'
          have hτ : τ = τ' :=
            hasPlaceType_unique hp hp'
          cases hτ
          rfl
  | add hv₁ hv₂ =>
      cases h₂ <;> rfl
  | sub hv₁ hv₂ =>
      cases h₂ <;> rfl
  | mul hv₁ hv₂ =>
      cases h₂ <;> rfl
  | eq hv₁ hv₂ =>
      cases h₂ <;> rfl
  | lt hv₁ hv₂ =>
      cases h₂ <;> rfl
  | not hv =>
      cases h₂ <;> rfl

end

end Cpp
