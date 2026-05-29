import CppFormalization.Cpp2.Validity.StateInvariantConcrete.FullAssembly
import CppFormalization.Cpp2.Preservation.DeclareRef.Preservation

namespace Cpp

/-!
# Closure.Transitions.Major.DeclareRefStrengtheningConnection

`DeclareRefDecomposition` に残っている ownership-side gap を、
`DeclareRefReadyStrong` の strengthening package で埋める接続層。

狙い:
- `topFrameBindingFresh σ x` を `Ready Γ σ x` から取り出す。
- Foundation 側ですでに theorem-backed になっている
  `ownership_after_declareRefState` / `concrete_after_declareRefState`
  を `DeclaresRef ...` の形へ持ち上げる。
- これにより、`DeclareRefDecomposition` の残り axioms を使わずに済む
  strong API を与える。
-/

/-- `Ready Γ σ x` と runtime-side freshness から top type frame witness を得る。 -/
private theorem topTypeFrameWitness_of_ready_and_scopeFresh
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareRefReadyStrong.Ready Γ σ x)
    (hsfresh : currentScopeFresh σ x) :
    ∃ Γfr, Γ.scopes[0]? = some Γfr := by
  cases hσ : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hσ] at hsfresh
  | cons σfr σrs =>
      cases hΓ : Γ.scopes with
      | nil =>
          have hdepth := h.concrete.frameDepth
          unfold frameDepthAgreement at hdepth
          simp [hΓ, hσ] at hdepth
      | cons Γfr Γrs =>
          exact ⟨Γfr, by simp⟩

/-- Strengthened ownership-side naming theorem for `declareRef`. -/
theorem declareRef_preserves_ownedAddressNamed_strong
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    DeclareRefReadyStrong.Ready Γ σ x →
    DeclaresRef σ τ x a σ' →
    ∀ {k addr},
      runtimeFrameOwnsAddress σ' k addr →
      ∃ y υ, runtimeFrameBindsObject σ' k y υ addr := by
  intro hready hdecl k addr hown
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  rcases topTypeFrameWitness_of_ready_and_scopeFresh
      (h := hready) (hsfresh := hsfresh) with ⟨Γfr, hΓ0⟩
  exact
    (DeclareRefReadyStrong.ownership_after_declareRefState
      (h := hready) (hΓ0 := hΓ0) (τ := τ) (a := a)).ownedAddressNamed hown

/-- Strengthened ref-not-owned theorem for `declareRef`. -/
theorem declareRef_preserves_refBindingsNeverOwned_strong
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    DeclareRefReadyStrong.Ready Γ σ x →
    DeclaresRef σ τ x a σ' →
    refBindingsNeverOwned σ' := by
  intro hready hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  rcases topTypeFrameWitness_of_ready_and_scopeFresh
      (h := hready) (hsfresh := hsfresh) with ⟨Γfr, hΓ0⟩
  exact
    (DeclareRefReadyStrong.ownership_after_declareRefState
      (h := hready) (hΓ0 := hΓ0) (τ := τ) (a := a)).refsNotOwned

/-- Strengthened owned-address naming theorem for `declareRef`. -/
theorem declareRef_preserves_allOwnedAddressesNamed_strong
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    DeclareRefReadyStrong.Ready Γ σ x →
    DeclaresRef σ τ x a σ' →
    allOwnedAddressesNamed σ' := by
  intro hready hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  rcases topTypeFrameWitness_of_ready_and_scopeFresh
      (h := hready) (hsfresh := hsfresh) with ⟨Γfr, hΓ0⟩
  exact
    (DeclareRefReadyStrong.ownership_after_declareRefState
      (h := hready) (hΓ0 := hΓ0) (τ := τ) (a := a)).ownedNamed

/-- Strongened full concrete-state preservation for `declareRef`. -/
theorem declareRef_concrete_state_of_decomposition_strong
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    DeclareRefReadyStrong.Ready Γ σ x →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ' := by
  intro hready hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  rcases topTypeFrameWitness_of_ready_and_scopeFresh
      (h := hready) (hsfresh := hsfresh) with ⟨Γfr, hΓ0⟩
  exact
    DeclareRefReadyStrong.concrete_after_declareRefState
      (h := hready) (hΓ0 := hΓ0) (τ := τ) (a := a)
      ⟨c, hheap, hty, halive⟩

/-- Alias of the strengthened full preservation theorem. -/
theorem declares_ref_preserves_scoped_typed_state_concrete_strong
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    DeclareRefReadyStrong.Ready Γ σ x →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ' := by
  intro hready hdecl
  exact declareRef_concrete_state_of_decomposition_strong hready hdecl

end Cpp
