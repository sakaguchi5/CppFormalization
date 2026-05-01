import CppFormalization.Cpp2.Typing.Stmt
import CppFormalization.Cpp2.Static.WellFormed
namespace Cpp

/-!
# Closure.Foundation.WellFormedFromTyping

Small structural facts saying that the ordinary expression/place typing
judgments imply the corresponding well-formedness predicates.

These facts are not specific to any external fragment.  They belong in the
Foundation layer and can be reused by concrete fragment certificates.
-/

mutual

/-- A typed place expression is structurally well-formed. -/
theorem wellFormedPlace_of_hasPlaceType
    {Γ : TypeEnv} {p : PlaceExpr} {τ : CppType} :
    HasPlaceType Γ p τ → WellFormedPlace p := by
  intro h
  cases h with
  | var _ =>
      simp [WellFormedPlace]
  | deref hv =>
      exact wellFormedValue_of_hasValueType hv

/-- A typed value expression is structurally well-formed. -/
theorem wellFormedValue_of_hasValueType
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ → WellFormedValue e := by
  intro h
  cases h with
  | litBool =>
      simp [WellFormedValue]
  | litInt =>
      simp [WellFormedValue]
  | load hp =>
      simpa [WellFormedValue] using wellFormedPlace_of_hasPlaceType hp
  | addrOf hp =>
      simpa [WellFormedValue] using wellFormedPlace_of_hasPlaceType hp
  | add h1 h2 =>
      exact ⟨wellFormedValue_of_hasValueType h1, wellFormedValue_of_hasValueType h2⟩
  | sub h1 h2 =>
      exact ⟨wellFormedValue_of_hasValueType h1, wellFormedValue_of_hasValueType h2⟩
  | mul h1 h2 =>
      exact ⟨wellFormedValue_of_hasValueType h1, wellFormedValue_of_hasValueType h2⟩
  | eq h1 h2 =>
      exact ⟨wellFormedValue_of_hasValueType h1, wellFormedValue_of_hasValueType h2⟩
  | lt h1 h2 =>
      exact ⟨wellFormedValue_of_hasValueType h1, wellFormedValue_of_hasValueType h2⟩
  | not h1 =>
      simp [WellFormedValue]
      exact wellFormedValue_of_hasValueType h1

end

end Cpp
