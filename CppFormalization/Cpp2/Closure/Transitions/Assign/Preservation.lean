import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcretePreservation
import CppFormalization.Cpp2.Lemmas.RuntimeState

namespace Cpp

/-!
# Closure.Transitions.Assign.Preservation

Canonical assign-transition preservation facts.

`Assigns` is a heap-write transition: it updates one live typed cell while
leaving scopes, bindings, ownership, and the fresh cursor structurally intact.
This file is the public assign-oriented home for the concrete state-preservation
proof formerly housed under `Closure.Transitions.Minor.AssignDecomposition`.
-/

theorem assigns_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ → HasPlaceType Γ p τ → PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ → Assigns σ p v σ' → objectBindingSound σ' := by
  intro hσ _ _ _ hassign k x υ a hbind
  rcases hassign with ⟨a0, c0, _, hheap0, halive0, _, rfl⟩
  have hbind_old : runtimeFrameBindsObject σ k x υ a := by
    simpa [runtimeFrameBindsObject, writeHeap] using hbind
  rcases hσ.objectBindingSound hbind_old with ⟨hown, hlive⟩
  refine ⟨by simpa [runtimeFrameOwnsAddress, writeHeap] using hown, ?_⟩
  rcases hlive with ⟨c, hheap, hty, halive⟩
  by_cases ha : a = a0
  · subst ha
    let c_new : Cell := { ty := c0.ty, value := some v, alive := c0.alive }
    refine ⟨c_new, ?_, ?_, halive0⟩
    · simp [writeHeap, c_new]
    · simp [hheap0] at hheap
      rw [← hty, ← hheap]
  · exact ⟨c, by simp [writeHeap, ha, hheap], hty, halive⟩

theorem assigns_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ → HasPlaceType Γ p τ → PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ → Assigns σ p v σ' → refBindingSound σ' := by
  intro hσ _ _ _ hassign k x υ a hbind
  rcases hassign with ⟨a0, c0, _, hheap0, halive0, _, rfl⟩
  have hbind_old : runtimeFrameBindsRef σ k x υ a := by
    simpa [runtimeFrameBindsRef, writeHeap] using hbind
  rcases hσ.refBindingSound hbind_old with ⟨c, hheap, hty, halive⟩
  by_cases ha : a = a0
  · subst ha
    let c_new : Cell := { ty := c0.ty, value := some v, alive := c0.alive }
    refine ⟨c_new, by simp [writeHeap, c_new], ?_, halive0⟩
    simp [hheap0] at hheap
    rw [← hty, ← hheap]
  · exact ⟨c, by simp [writeHeap, ha, hheap], hty, halive⟩

section WriteHeapHelpers

private theorem runtimeFrameBindsObject_writeHeap_iff
    {σ : State} {a : Nat} {c : Cell}
    {k : Nat} {x : Ident} {τ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (writeHeap σ a c) k x τ addr ↔
      runtimeFrameBindsObject σ k x τ addr := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsObject, writeHeap] using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsObject, writeHeap] using hk, hb⟩

private theorem runtimeFrameBindsRef_writeHeap_iff
    {σ : State} {a : Nat} {c : Cell}
    {k : Nat} {x : Ident} {τ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (writeHeap σ a c) k x τ addr ↔
      runtimeFrameBindsRef σ k x τ addr := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsRef, writeHeap] using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsRef, writeHeap] using hk, hb⟩

private theorem runtimeFrameOwnsAddress_writeHeap_iff
    {σ : State} {a : Nat} {c : Cell}
    {k : Nat} {addr : Nat} :
    runtimeFrameOwnsAddress (writeHeap σ a c) k addr ↔
      runtimeFrameOwnsAddress σ k addr := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hm⟩
    exact ⟨fr, by simpa [runtimeFrameOwnsAddress, writeHeap] using hk, hm⟩
  · rcases h with ⟨fr, hk, hm⟩
    exact ⟨fr, by simpa [runtimeFrameOwnsAddress, writeHeap] using hk, hm⟩

private theorem heapLiveTypedAt_writeHeap_preserved
    {σ : State} {aWrite : Nat} {cWrite : Cell}
    {a : Nat} {τ : CppType} :
    heapLiveTypedAt σ a τ →
    a = aWrite → cWrite.ty = τ → cWrite.alive = true →
    heapLiveTypedAt (writeHeap σ aWrite cWrite) a τ := by
  intro _ ha hty halive
  subst ha
  exact ⟨cWrite, by simp [writeHeap], hty, halive⟩

private theorem heapLiveTypedAt_writeHeap_preserved_of_ne
    {σ : State} {aWrite : Nat} {cWrite : Cell}
    {a : Nat} {τ : CppType} :
    a ≠ aWrite →
    heapLiveTypedAt σ a τ →
    heapLiveTypedAt (writeHeap σ aWrite cWrite) a τ := by
  intro hne h
  rcases h with ⟨c, hheap, hty, halive⟩
  exact ⟨c, by simpa [writeHeap, hne] using hheap, hty, halive⟩

private theorem heapLiveTypedAt_assigns_preserved
    {σ σ' : State} {p : PlaceExpr} {v : Value}
    {a : Nat} {τ : CppType} :
    Assigns σ p v σ' →
    heapLiveTypedAt σ a τ →
    heapLiveTypedAt σ' a τ := by
  intro hassign hlive
  rcases hassign with ⟨a0, c0, _hplace, hheap0, halive0, _hcompat, rfl⟩
  by_cases ha : a = a0
  · subst ha
    rcases hlive with ⟨c, hheap, hty, halive⟩
    have hc : c = c0 := by
      rw [hheap0] at hheap
      injection hheap.symm
    subst c
    exact heapLiveTypedAt_writeHeap_preserved
      ⟨c0, hheap0, hty, halive⟩ rfl hty (by simp [halive0])
  · rcases hlive with ⟨c, hheap, hty, halive⟩
    refine ⟨c, ?_, hty, halive⟩
    simp [writeHeap, ha, hheap]

private theorem heapInitializedValuesTyped_after_assigns
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    Assigns σ p v σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ hassign
  rcases hassign with ⟨a0, c0, _hplace, hheap0, halive0, hcompat0, rfl⟩
  intro a c w hheap hval
  by_cases ha : a = a0
  · subst ha
    have hc : c = { c0 with value := some v } := by
      apply Option.some.inj
      simpa [writeHeap] using hheap.symm
    subst hc
    have hw : w = v := by
      apply Option.some.inj
      simpa using hval.symm
    subst hw
    simpa using hcompat0
  · have hheapOld : σ.heap a = some c := by
      simpa [writeHeap, ha] using hheap
    exact hσ.heapStoredValuesTyped a c w hheapOld hval

private theorem assigned_addr_ne_next
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    Assigns σ p v σ' →
    ∀ {a0 c0},
      BigStepPlace σ p a0 →
      σ.heap a0 = some c0 →
      a0 ≠ σ.next := by
  intro hσ hassign a0 c0 _ hheap
  intro hEq
  subst hEq
  rcases hσ.nextFresh with ⟨hheapNone, _⟩
  rw [hheapNone] at hheap
  simp at hheap

end WriteHeapHelpers

private theorem framewiseDeclBindingExact_writeHeap
    {Γ : TypeEnv} {σ : State} {a : Nat} {c : Cell} :
    framewiseDeclBindingExact Γ (writeHeap σ a c) ↔
      framewiseDeclBindingExact Γ σ := by
  constructor <;> intro h k Γfr σfr hΓ hσfr
  · have hσold : σ.scopes[k]? = some σfr := by
      simpa [writeHeap] using hσfr
    exact h k Γfr σfr hΓ hσold
  · have hσnew : (writeHeap σ a c).scopes[k]? = some σfr := by
      simpa [writeHeap] using hσfr
    exact h k Γfr σfr hΓ hσnew

theorem assigns_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ → HasPlaceType Γ p τ → PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ → Assigns σ p v σ' → ScopedTypedStateConcrete Γ σ' := by
  intro hσ hpty hpready hvcompat hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  refine
    { frameDepth := by
        simpa [frameDepthAgreement, writeHeap] using hσ.frameDepth
      namesExact := by
        exact (framewiseDeclBindingExact_writeHeap (Γ := Γ) (σ := σ)
          (a := a0) (c := { c0 with value := some v })).2 hσ.namesExact
      shadowing := by
        intro x d hdecl
        rcases hσ.shadowing x d hdecl with ⟨b, hb, hmatch⟩
        exact ⟨b, by simpa [lookupBinding_writeHeap] using hb, hmatch⟩
      objectDeclRealized := by
        intro k x τ hdecl
        rcases hσ.objectDeclRealized hdecl with ⟨addr, hbind, hown, hlive⟩
        refine ⟨addr, ?_, ?_, ?_⟩
        · exact (runtimeFrameBindsObject_writeHeap_iff
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (x := x) (τ := τ) (addr := addr)).2 hbind
        · exact (runtimeFrameOwnsAddress_writeHeap_iff
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (addr := addr)).2 hown
        · exact heapLiveTypedAt_assigns_preserved
            (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
            (p := p) (v := v) (a := addr) (τ := τ)
            ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩ hlive
      refDeclRealized := by
        intro k x τ hdecl
        rcases hσ.refDeclRealized hdecl with ⟨addr, hbind, hlive⟩
        refine ⟨addr, ?_, ?_⟩
        · exact (runtimeFrameBindsRef_writeHeap_iff
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (x := x) (τ := τ) (addr := addr)).2 hbind
        · exact heapLiveTypedAt_assigns_preserved
            (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
            (p := p) (v := v) (a := addr) (τ := τ)
            ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩ hlive
      objectBindingSound :=
        assigns_preserves_objectBindingSound
          (Γ := Γ) (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
          (p := p) (τ := τ) (v := v) hσ hpty hpready hvcompat
          ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
      refBindingSound :=
        assigns_preserves_refBindingSound
          (Γ := Γ) (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
          (p := p) (τ := τ) (v := v) hσ hpty hpready hvcompat
          ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
      ownedAddressNamed := by
        intro k addr hown
        exact hσ.ownedAddressNamed <|
          (runtimeFrameOwnsAddress_writeHeap_iff
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (addr := addr)).1 hown
      refsNotOwned := by
        intro k fr x τ addr hk href hmem
        let hown_new : runtimeFrameOwnsAddress (writeHeap σ a0 { c0 with value := some v }) k addr := ⟨fr, hk, hmem⟩
        have hown_old : runtimeFrameOwnsAddress σ k addr :=
          (runtimeFrameOwnsAddress_writeHeap_iff (a := a0) (c := { c0 with value := some v })).1 hown_new
        rcases hown_old with ⟨fr_old, hk_old, hmem_old⟩
        have hfr_eq : fr = fr_old := by
          simp [writeHeap] at hk
          rw [hk] at hk_old
          injection hk_old
        subst hfr_eq
        exact hσ.refsNotOwned k fr x τ addr hk_old href hmem
      objectsOwned := by
        intro k x τ addr hbind
        exact (runtimeFrameOwnsAddress_writeHeap_iff
          (σ := σ) (a := a0) (c := { c0 with value := some v })
          (k := k) (addr := addr)).2 <|
            hσ.objectsOwned k x τ addr <|
              (runtimeFrameBindsObject_writeHeap_iff
                (σ := σ) (a := a0) (c := { c0 with value := some v })
                (k := k) (x := x) (τ := τ) (addr := addr)).1 hbind
      ownedNoDupPerFrame := by
        intro k fr hk
        exact hσ.ownedNoDupPerFrame k fr <|
          by simpa [writeHeap, runtimeFrameOwnsAddress] using hk
      ownedDisjoint := by
        intro i j fi fj addr hij hi hj hai haj
        exact hσ.ownedDisjoint i j fi fj addr hij
          (by simpa [writeHeap] using hi)
          (by simpa [writeHeap] using hj) hai haj
      ownedNamed := by
        intro k addr hown
        have hown_old : runtimeFrameOwnsAddress σ k addr :=
          (runtimeFrameOwnsAddress_writeHeap_iff (a := a0) (c := { c0 with value := some v })).1 hown
        rcases hσ.ownedNamed k addr hown_old with ⟨x, τ_obj, hbind_old⟩
        refine ⟨x, τ_obj, ?_⟩
        exact (runtimeFrameBindsObject_writeHeap_iff (a := a0) (c := { c0 with value := some v })).2 hbind_old
      heapStoredValuesTyped :=
        heapInitializedValuesTyped_after_assigns
          (Γ := Γ) (σ := σ)
          (p := p) (v := v)
          hσ
          ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
      nextFresh := by
        rcases hσ.nextFresh with ⟨hheapNone, hlocals⟩
        refine ⟨?_, ?_⟩
        · have hne : a0 ≠ σ.next := by
            exact assigned_addr_ne_next (Γ := Γ) (σ := σ)
              hσ ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩ hplace hheap0
          simpa [writeHeap, hne, eq_comm] using hheapNone
        · intro k fr hk
          simpa [writeHeap] using hlocals k fr hk
      refTargetsAvoidInnerOwned := by
        intro k x τ addr j href hjk hown
        exact hσ.refTargetsAvoidInnerOwned
          ((runtimeFrameBindsRef_writeHeap_iff
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (x := x) (τ := τ) (addr := addr)).1 href)
          hjk
          ((runtimeFrameOwnsAddress_writeHeap_iff
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := j) (addr := addr)).1 hown) }

end Cpp
