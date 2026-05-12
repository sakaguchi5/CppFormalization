import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteDeclTransport
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteRecomputedCursor
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteReadyTransport

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteDeclRealization

Lower realization lemmas extracted from full assembly.

This file hosts the two kinds of statements that were too valuable to lose but
too low-level to keep buried inside `StateInvariantConcreteFullAssembly`:
- support transport lemmas for heap/live and ref-binding forwarding
- old/new declaration realization lemmas for object/ref updates, including the
  recomputed-cursor wrappers

The purely local one-shot nonempty / top-frame-shape helpers remain deleted.
-/

section DeclRealizationSupport
@[simp] theorem heapLiveTypedAt_declareRefState_iff
    {σ : State} {τ : CppType} {x : Ident} {r : Nat} {a : Nat} {υ : CppType} :
    heapLiveTypedAt (declareRefState σ τ x r) a υ ↔ heapLiveTypedAt σ a υ := by
  constructor <;> intro h <;> rcases h with ⟨c, hc, hty, halive⟩
  · refine ⟨c, ?_, hty, halive⟩
    -- 左辺の heap を右辺（σ.heap）に書き換える
    rw [declareRefState_heap] at hc
    exact hc
  · refine ⟨c, ?_, hty, halive⟩
    -- ゴールの heap を σ.heap に書き換える
    rw [declareRefState_heap]
    exact hc

 theorem heapLiveTypedAt_declareObjectState_of_ne
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat} {υ : CppType} :
    a ≠ σ.next →
    heapLiveTypedAt σ a υ →
    heapLiveTypedAt (declareObjectState σ τ x ov) a υ := by
  intro hne hlive
  rcases hlive with ⟨c, hc, hty, halive⟩
  refine ⟨c, ?_, hty, halive⟩
  rw [declareObjectState_heap_other σ τ x ov hne]
  exact hc

@[simp] theorem heapLiveTypedAt_declareObjectState_self
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    heapLiveTypedAt (declareObjectState σ τ x ov) σ.next τ := by
  refine ⟨{ ty := τ, value := ov, alive := true }, ?_, rfl, rfl⟩
  simp

 theorem runtimeFrameOwnsAddress_ne_next_of_nextFresh
    {σ : State} {k : Nat} {a : Nat} :
    nextFreshAgainstOwned σ →
    runtimeFrameOwnsAddress σ k a →
    a ≠ σ.next := by
  intro hfresh hown
  rcases hfresh with ⟨_, hlocals⟩
  rcases hown with ⟨fr, hk, ha⟩
  intro hEq
  subst a
  exact hlocals k fr hk ha

 theorem heapLiveTypedAt_ne_next_of_nextFresh
    {σ : State} {a : Nat} {τ : CppType} :
    nextFreshAgainstOwned σ →
    heapLiveTypedAt σ a τ →
    a ≠ σ.next := by
  intro hfresh hlive
  rcases hfresh with ⟨hheapNone, _⟩
  rcases hlive with ⟨c, hc, _, _⟩
  intro hEq
  subst a
  rw [hheapNone] at hc
  simp at hc

theorem ownedAndLive_declareObjectState_of_oldOwned
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k a : Nat} {τ' : CppType} :
    nextFreshAgainstOwned σ →
    runtimeFrameOwnsAddress σ k a →
    heapLiveTypedAt σ a τ' →
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  intro hfresh hown hlive
  have hane : a ≠ σ.next :=
    runtimeFrameOwnsAddress_ne_next_of_nextFresh hfresh hown
  exact ⟨
    runtimeFrameOwnsAddress_declareObjectState_forward hown,
    heapLiveTypedAt_declareObjectState_of_ne hane hlive⟩

theorem heapLiveTypedAt_declareObjectState_of_oldLive
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat} {τ' : CppType} :
    nextFreshAgainstOwned σ →
    heapLiveTypedAt σ a τ' →
    heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  intro hfresh hlive
  have hane : a ≠ σ.next :=
    heapLiveTypedAt_ne_next_of_nextFresh hfresh hlive
  exact heapLiveTypedAt_declareObjectState_of_ne hane hlive

end DeclRealizationSupport

namespace DeclareObjectReadyStrong

theorem transport_old_object_realization_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclObject Γ k x' τ') :
    ∃ a,
      runtimeFrameBindsObject (declareObjectState σ τ x ov) k x' τ' a ∧
      runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  rcases h.concrete.objectDeclRealized hdeclOld with ⟨a, hobjOld, hownOld, hliveOld⟩
  have hobjNew := runtimeFrameBindsObject_declareObjectState_forward_of_topFresh
    (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hobjOld
  have hrealNew := ownedAndLive_declareObjectState_of_oldOwned
    (σ := σ) (τ := τ) (x := x) (ov := ov)
    h.concrete.nextFresh hownOld hliveOld
  exact ⟨a, hobjNew, hrealNew.1, hrealNew.2⟩

theorem transport_old_ref_realization_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclRef Γ k x' τ') :
    ∃ a,
      runtimeFrameBindsRef (declareObjectState σ τ x ov) k x' τ' a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  rcases h.concrete.refDeclRealized hdeclOld with ⟨a, hrefOld, hliveOld⟩
  have hrefNew := runtimeFrameBindsRef_declareObjectState_forward_of_topFresh
    (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hrefOld
  have hliveNew := heapLiveTypedAt_declareObjectState_of_oldLive
    (σ := σ) (τ := τ) (x := x) (ov := ov)
    h.concrete.nextFresh hliveOld
  exact ⟨a, hrefNew, hliveNew⟩


theorem runtimeFrameOwnsAddress_declareObjectState_zero_next
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 σ.next := by
  exact declareObjectState_api_runtimeFrameOwnsAddress_zero_new

theorem declare_new_object_realization_after_declareObjectState
    {σ : State} {x : Ident}
    {τ : CppType} {ov : Option Value} :
    ∃ a,
      runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ a ∧
      runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ := by
  refine ⟨σ.next, ?_, ?_, ?_⟩
  · exact declareObjectState_api_runtimeFrameBindsObject_top_new
  · exact runtimeFrameOwnsAddress_declareObjectState_zero_next
  · exact heapLiveTypedAt_declareObjectState_self


 theorem objectDeclRealized_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    ∀ {k x' τ'},
      typeFrameDeclObject (declareTypeObject Γ x τ) k x' τ' →
      ∃ a,
        runtimeFrameBindsObject (declareObjectState σ τ x ov) k x' τ' a ∧
        runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k a ∧
        heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      by_cases hx' : x' = x
      · subst x'
        have hτ' : τ' = τ :=
          typeFrameDeclObject_declareTypeObject_zero_self_type hdecl
        subst τ'
        exact declare_new_object_realization_after_declareObjectState
      · have hdeclOld : typeFrameDeclObject Γ 0 x' τ' :=
          typeFrameDeclObject_declareTypeObject_zero_old_of_ne hx' hdecl
        exact
          transport_old_object_realization_after_declareObjectState
            (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclObject Γ k.succ x' τ' :=
        (typeFrameDeclObject_declareTypeObject_succ_iff).1 hdecl
      exact
        transport_old_object_realization_after_declareObjectState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld


 theorem refDeclRealized_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    ∀ {k x' τ'},
      typeFrameDeclRef (declareTypeObject Γ x τ) k x' τ' →
      ∃ a,
        runtimeFrameBindsRef (declareObjectState σ τ x ov) k x' τ' a ∧
        heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      have hdeclOld : typeFrameDeclRef Γ 0 x' τ' :=
        typeFrameDeclRef_declareTypeObject_zero_old hdecl
      exact
        transport_old_ref_realization_after_declareObjectState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclRef Γ k.succ x' τ' :=
        (typeFrameDeclRef_declareTypeObject_succ_iff).1 hdecl
      exact
        transport_old_ref_realization_after_declareObjectState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld


end DeclareObjectReadyStrong

namespace DeclareRefReadyStrong

theorem transport_old_object_realization_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclObject Γ k x' τ') :
    ∃ addr,
      runtimeFrameBindsObject (declareRefState σ τ x a) k x' τ' addr ∧
      runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr ∧
      heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  rcases h.concrete.objectDeclRealized hdeclOld with
    ⟨addr, hobjOld, hownOld, hliveOld⟩
  have hobjNew :
      runtimeFrameBindsObject (declareRefState σ τ x a) k x' τ' addr :=
    runtimeFrameBindsObject_declareRefState_forward_of_topFresh
      (σ := σ) (τ := τ) (x := x) (a := a)
      (h.topFrameFresh hΓ0) hobjOld
  have hownNew :
      runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr :=
    (runtimeFrameOwnsAddress_declareRefState_iff
      (σ := σ) (τ := τ) (x := x) (a := a)
      (k := k) (addr := addr)).2 hownOld
  have hliveNew :
      heapLiveTypedAt (declareRefState σ τ x a) addr τ' :=
    (heapLiveTypedAt_declareRefState_iff
      (σ := σ) (τ := τ) (x := x) (r := a)
      (a := addr) (υ := τ')).2 hliveOld
  exact ⟨addr, hobjNew, hownNew, hliveNew⟩

theorem transport_old_ref_realization_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclRef Γ k x' τ') :
    ∃ addr,
      runtimeFrameBindsRef (declareRefState σ τ x a) k x' τ' addr ∧
      heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  rcases h.concrete.refDeclRealized hdeclOld with
    ⟨addr, hrefOld, hliveOld⟩
  have hrefNew :
      runtimeFrameBindsRef (declareRefState σ τ x a) k x' τ' addr :=
    runtimeFrameBindsRef_declareRefState_forward_of_topFresh
      (σ := σ) (τ := τ) (x := x) (a := a)
      (h.topFrameFresh hΓ0) hrefOld
  have hliveNew :
      heapLiveTypedAt (declareRefState σ τ x a) addr τ' :=
    (heapLiveTypedAt_declareRefState_iff
      (σ := σ) (τ := τ) (x := x) (r := a)
      (a := addr) (υ := τ')).2 hliveOld
  exact ⟨addr, hrefNew, hliveNew⟩

theorem declare_new_ref_realization_after_declareRefState
    {σ : State} {x : Ident} {τ : CppType} {a : Nat}
    (haLive : heapLiveTypedAt σ a τ) :
    ∃ addr,
      runtimeFrameBindsRef (declareRefState σ τ x a) 0 x τ addr ∧
      heapLiveTypedAt (declareRefState σ τ x a) addr τ := by
  refine ⟨a, ?_, ?_⟩
  · exact declareRefState_api_runtimeFrameBindsRef_top_new
  · exact
      (heapLiveTypedAt_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (r := a)
        (a := a) (υ := τ)).2 haLive

theorem objectDeclRealized_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat} :
    ∀ {k x' τ'},
      typeFrameDeclObject (declareTypeRef Γ x τ) k x' τ' →
      ∃ addr,
        runtimeFrameBindsObject (declareRefState σ τ x a) k x' τ' addr ∧
        runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr ∧
        heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      have hdeclOld : typeFrameDeclObject Γ 0 x' τ' :=
        typeFrameDeclObject_declareTypeRef_zero_old hdecl
      exact
        transport_old_object_realization_after_declareRefState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclObject Γ k.succ x' τ' :=
        (typeFrameDeclObject_declareTypeRef_succ_iff).1 hdecl
      exact
        transport_old_object_realization_after_declareRefState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld

theorem refDeclRealized_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    (haLive : heapLiveTypedAt σ a τ) :
    ∀ {k x' τ'},
      typeFrameDeclRef (declareTypeRef Γ x τ) k x' τ' →
      ∃ addr,
        runtimeFrameBindsRef (declareRefState σ τ x a) k x' τ' addr ∧
        heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      by_cases hx' : x' = x
      · subst x'
        have hτ' : τ' = τ :=
          typeFrameDeclRef_declareTypeRef_zero_self_type hdecl
        subst τ'
        exact declare_new_ref_realization_after_declareRefState
          (σ := σ) (x := x) (τ := τ) (a := a) haLive
      · have hdeclOld : typeFrameDeclRef Γ 0 x' τ' :=
          typeFrameDeclRef_declareTypeRef_zero_old_of_ne hx' hdecl
        exact
          transport_old_ref_realization_after_declareRefState
            (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclRef Γ k.succ x' τ' :=
        (typeFrameDeclRef_declareTypeRef_succ_iff).1 hdecl
      exact
        transport_old_ref_realization_after_declareRefState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld



end DeclareRefReadyStrong

namespace DeclareObjectReadyRecomputed

theorem transport_old_object_realization_after_declareObjectStateWithNext
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {Γfr : TypeFrame}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclObject Γ k x' τ') :
    ∃ a,
      runtimeFrameBindsObject
        (declareObjectStateWithNext σ τ x ov h.cursor.addr) k x' τ' a ∧
      runtimeFrameOwnsAddress
        (declareObjectStateWithNext σ τ x ov h.cursor.addr) k a ∧
      heapLiveTypedAt
        (declareObjectStateWithNext σ τ x ov h.cursor.addr) a τ' := by
  rcases
    (DeclareObjectReadyStrong.transport_old_object_realization_after_declareObjectState
      (h := h.ready) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld)
    with ⟨a, hobjOld, hownOld, hliveOld⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa [runtimeFrameBindsObject, scopes_declareObjectStateWithNext_eq_old] using hobjOld
  · simpa [runtimeFrameOwnsAddress, scopes_declareObjectStateWithNext_eq_old] using hownOld
  · simpa [heapLiveTypedAt, heap_declareObjectStateWithNext_eq_old] using hliveOld

theorem transport_old_ref_realization_after_declareObjectStateWithNext
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {Γfr : TypeFrame}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclRef Γ k x' τ') :
    ∃ a,
      runtimeFrameBindsRef
        (declareObjectStateWithNext σ τ x ov h.cursor.addr) k x' τ' a ∧
      heapLiveTypedAt
        (declareObjectStateWithNext σ τ x ov h.cursor.addr) a τ' := by
  rcases
    (DeclareObjectReadyStrong.transport_old_ref_realization_after_declareObjectState
      (h := h.ready) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld)
    with ⟨a, hrefOld, hliveOld⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [runtimeFrameBindsRef, scopes_declareObjectStateWithNext_eq_old] using hrefOld
  · simpa [heapLiveTypedAt, heap_declareObjectStateWithNext_eq_old] using hliveOld

theorem declare_new_object_realization_after_declareObjectStateWithNext
    {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (aNext : Nat) :
    ∃ a,
      runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 x τ a ∧
      runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 a ∧
      heapLiveTypedAt (declareObjectStateWithNext σ τ x ov aNext) a τ := by
  rcases
    (DeclareObjectReadyStrong.declare_new_object_realization_after_declareObjectState)
    with ⟨a, hobjOld, hownOld, hliveOld⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa [runtimeFrameBindsObject, scopes_declareObjectStateWithNext_eq_old] using hobjOld
  · simpa [runtimeFrameOwnsAddress, scopes_declareObjectStateWithNext_eq_old] using hownOld
  · simpa [heapLiveTypedAt, heap_declareObjectStateWithNext_eq_old] using hliveOld

theorem objectDeclRealized_after_declareObjectStateWithNext
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {Γfr : TypeFrame}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    ∀ {k x' τ'},
      typeFrameDeclObject (declareTypeObject Γ x τ) k x' τ' →
      ∃ a,
        runtimeFrameBindsObject
          (declareObjectStateWithNext σ τ x ov h.cursor.addr) k x' τ' a ∧
        runtimeFrameOwnsAddress
          (declareObjectStateWithNext σ τ x ov h.cursor.addr) k a ∧
        heapLiveTypedAt
          (declareObjectStateWithNext σ τ x ov h.cursor.addr) a τ' := by
  intro k x' τ' hdecl
  rcases
    (DeclareObjectReadyStrong.objectDeclRealized_after_declareObjectState
      (h := h.ready) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdecl)
    with ⟨a, hobjOld, hownOld, hliveOld⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa [runtimeFrameBindsObject, scopes_declareObjectStateWithNext_eq_old] using hobjOld
  · simpa [runtimeFrameOwnsAddress, scopes_declareObjectStateWithNext_eq_old] using hownOld
  · simpa [heapLiveTypedAt, heap_declareObjectStateWithNext_eq_old] using hliveOld

theorem refDeclRealized_after_declareObjectStateWithNext
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {Γfr : TypeFrame}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    ∀ {k x' τ'},
      typeFrameDeclRef (declareTypeObject Γ x τ) k x' τ' →
      ∃ a,
        runtimeFrameBindsRef
          (declareObjectStateWithNext σ τ x ov h.cursor.addr) k x' τ' a ∧
        heapLiveTypedAt
          (declareObjectStateWithNext σ τ x ov h.cursor.addr) a τ' := by
  intro k x' τ' hdecl
  rcases
    (DeclareObjectReadyStrong.refDeclRealized_after_declareObjectState
      (h := h.ready) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdecl)
    with ⟨a, hrefOld, hliveOld⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [runtimeFrameBindsRef, scopes_declareObjectStateWithNext_eq_old] using hrefOld
  · simpa [heapLiveTypedAt, heap_declareObjectStateWithNext_eq_old] using hliveOld

end DeclareObjectReadyRecomputed
end Cpp
