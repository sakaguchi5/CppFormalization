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
  constructor <;> intro h
  · rcases h with ⟨c, hc, hty, halive⟩
    refine ⟨c, ?_, hty, halive⟩
    simpa [declareRefState] using hc
  · rcases h with ⟨c, hc, hty, halive⟩
    refine ⟨c, ?_, hty, halive⟩
    simpa [declareRefState] using hc

 theorem heapLiveTypedAt_declareObjectState_of_ne
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat} {υ : CppType} :
    a ≠ σ.next →
    heapLiveTypedAt σ a υ →
    heapLiveTypedAt (declareObjectState σ τ x ov) a υ := by
  intro hne hlive
  rcases hlive with ⟨c, hc, hty, halive⟩
  refine ⟨c, ?_, hty, halive⟩
  simpa [declareObjectState_heap_other (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) hne] using hc

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

 theorem runtimeFrameBindsRef_top_name_ne_declared_of_topFresh
    {σ : State} {x y : Ident} {fr0 : ScopeFrame} {frs : List ScopeFrame}
    {υ : CppType} {addr : Nat}
    (hfresh : topFrameBindingFresh σ x)
    (hsc : σ.scopes = fr0 :: frs)
    (hb : fr0.binds y = some (.ref υ addr)) :
    y ≠ x := by
  intro hEq
  subst y
  rw [topFrameBindingFresh_zero_of_cons (σ := σ) (x := x) (fr0 := fr0) (frs := frs) hfresh hsc] at hb
  simp at hb

 theorem runtimeFrameBindsRef_declareRefState_zero_new
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[0]? = some fr) :
    runtimeFrameBindsRef (declareRefState σ τ x a) 0 x τ a := by
  refine ⟨fr, hk, ?_⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [declareRefState, scopes_bindTopBinding, hsc] at hk
      subst fr
      simp
  | cons fr0 frs =>
      rcases declareRefState_lookup_zero_frame_of_cons
        (σ := σ) (τ := τ) (x := x) (a := a)
        (fr0 := fr0) (frs := frs) hsc hk with rfl
      simp

 theorem runtimeFrameBindsRef_declareRefState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef σ k y υ addr →
    runtimeFrameBindsRef (declareRefState σ τ x a) k y υ addr := by
  intro href
  rcases href with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero => simp [hsc] at hk
      | succ k => simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [hsc] at hk
          subst fr
          have hyx : y ≠ x :=
            runtimeFrameBindsRef_top_name_ne_declared_of_topFresh
              (σ := σ) (x := x) (y := y) (fr0 := fr0) (frs := frs)
              (υ := υ) (addr := addr) hfresh hsc hb
          refine ⟨
            { fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z },
            ?_, ?_⟩
          · simp [declareRefState, scopes_bindTopBinding, hsc]
          · simpa [hyx] using hb
      | succ k =>
          refine ⟨fr, ?_, hb⟩
          exact (declareRefState_lookup_succ_iff
            (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (fr := fr)).2 hk

 theorem runtimeFrameBindsRef_declareObjectState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef σ k y υ addr →
    runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ addr := by
  intro href
  rcases href with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero => simp [hsc] at hk
      | succ k => simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [hsc] at hk
          subst fr
          have hyx : y ≠ x :=
            runtimeFrameBindsRef_top_name_ne_declared_of_topFresh
              (σ := σ) (x := x) (y := y) (fr0 := fr0) (frs := frs)
              (υ := υ) (addr := addr) hfresh hsc hb
          refine ⟨
            { fr0 with
              binds := fun z => if z = x then some (.object τ σ.next) else fr0.binds z,
              locals := σ.next :: fr0.locals },
            ?_, ?_⟩
          · simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc]
          · simpa [hyx] using hb
      | succ k =>
          refine ⟨fr, ?_, hb⟩
          exact (declareObjectState_lookup_succ_iff
            (σ := σ) (τ := τ) (x := x) (ov := ov) (k := k) (fr := fr)).2 hk
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
  have hownNew := runtimeFrameOwnsAddress_declareObjectState_forward
    (σ := σ) (τ := τ) (x := x) (ov := ov) hownOld
  have hane : a ≠ σ.next :=
    runtimeFrameOwnsAddress_ne_next_of_nextFresh
      (σ := σ) (k := k) (a := a) h.concrete.nextFresh hownOld
  have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
    (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
  exact ⟨a, hobjNew, hownNew, hliveNew⟩

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
  have hane : a ≠ σ.next :=
    heapLiveTypedAt_ne_next_of_nextFresh
      (σ := σ) (a := a) (τ := τ') h.concrete.nextFresh hliveOld
  have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
    (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
  exact ⟨a, hrefNew, hliveNew⟩


theorem runtimeFrameOwnsAddress_declareObjectState_zero_next
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 σ.next := by
  unfold runtimeFrameOwnsAddress
  have hkσ0 : ∃ fr, (declareObjectState σ τ x ov).scopes[0]? = some fr := by
    cases hσ : σ.scopes <;>
      simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hσ]
  rcases hkσ0 with ⟨frσ0, hkσ0⟩
  refine ⟨frσ0, hkσ0, ?_⟩
  cases hσ : σ.scopes <;>
    simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hσ] at hkσ0 ⊢
  -- 1. frσ0 を具体的な構造体の内容で置き換える
  subst frσ0
  -- 2. リストの先頭に σ.next があることを証明する
  case nil =>
    simp
  case cons =>
    subst frσ0
    simp

theorem declare_new_object_realization_after_declareObjectState
    {σ : State} {x : Ident}
    {τ : CppType} {ov : Option Value} :
    ∃ a,
      runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ a ∧
      runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ := by
  have hkσ0 : ∃ fr, (declareObjectState σ τ x ov).scopes[0]? = some fr := by
    cases hσ : σ.scopes <;>
      simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hσ]
  rcases hkσ0 with ⟨frσ0, hkσ0⟩
  have hobj : runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next :=
    runtimeFrameBindsObject_declareObjectState_zero_new
      (σ := σ) (τ := τ) (x := x) (ov := ov) hkσ0
  refine ⟨σ.next, hobj, ?_, ?_⟩
  · exact runtimeFrameOwnsAddress_declareObjectState_zero_next
      (σ := σ) (τ := τ) (x := x) (ov := ov)
  · simp


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
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases k with
  | zero =>
      cases hsc : Γ.scopes with
      | nil =>
          simp [hsc] at hΓ0
      | cons fr0 frs =>
          simp [declareTypeObject, insertTopDecl, hsc] at hk
          subst Γfr'
          by_cases hx' : x' = x
          · subst x'
            have hτ' : τ' = τ := by
              have : some (DeclInfo.object τ) = some (DeclInfo.object τ') := by
                simpa using hb
              injection this with h_decl_eq
              injection h_decl_eq with h_type_eq
              exact h_type_eq.symm
            subst τ'
            have hkσ0 : ∃ fr, (declareObjectState σ τ x ov).scopes[0]? = some fr := by
              cases hσ : σ.scopes <;>
                simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hσ]
            rcases hkσ0 with ⟨frσ0, hkσ0⟩
            have hobj : runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next :=
              runtimeFrameBindsObject_declareObjectState_zero_new
                (σ := σ) (τ := τ) (x := x) (ov := ov) hkσ0
            refine ⟨σ.next, hobj, ?_, ?_⟩
            · exact allObjectBindingsOwned_declareObjectState
                (σ := σ) (τ := τ) (x := x) (ov := ov) h.concrete.objectsOwned _ _ _ _ hobj
            · simp
          · have hbOld : fr0.decls x' = some (.object τ') := by
              simpa [hx'] using hb
            have hdeclOld : typeFrameDeclObject Γ 0 x' τ' := ⟨fr0, by simp [hsc], hbOld⟩
            rcases h.concrete.objectDeclRealized hdeclOld with ⟨a, hobjOld, hownOld, hliveOld⟩
            have hobjNew := runtimeFrameBindsObject_declareObjectState_forward_of_topFresh
              (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hobjOld
            have hownNew := runtimeFrameOwnsAddress_declareObjectState_forward
              (σ := σ) (τ := τ) (x := x) (ov := ov) hownOld
            have hane : a ≠ σ.next :=
              runtimeFrameOwnsAddress_ne_next_of_nextFresh (σ := σ) (k := 0) (a := a) h.concrete.nextFresh hownOld
            have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
              (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
            exact ⟨a, hobjNew, hownNew, hliveNew⟩
  | succ k =>
      have hkOld : Γ.scopes[k.succ]? = some Γfr' := by
        rwa [scopes_declareTypeObject_succ_iff] at hk
      have hdeclOld : typeFrameDeclObject Γ k.succ x' τ' := ⟨Γfr', hkOld, hb⟩
      rcases h.concrete.objectDeclRealized hdeclOld with ⟨a, hobjOld, hownOld, hliveOld⟩
      have hobjNew := runtimeFrameBindsObject_declareObjectState_forward_of_topFresh
        (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hobjOld
      have hownNew := runtimeFrameOwnsAddress_declareObjectState_forward
        (σ := σ) (τ := τ) (x := x) (ov := ov) hownOld
      have hane : a ≠ σ.next :=
        runtimeFrameOwnsAddress_ne_next_of_nextFresh (σ := σ) (k := k.succ) (a := a) h.concrete.nextFresh hownOld
      have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
        (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
      exact ⟨a, hobjNew, hownNew, hliveNew⟩

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
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases k with
  | zero =>
      cases hsc : Γ.scopes with
      | nil =>
          simp [hsc] at hΓ0
      | cons fr0 frs =>
          simp [declareTypeObject, insertTopDecl, hsc] at hk
          subst Γfr'
          have hx' : x' ≠ x := by
            intro hEq
            subst x'
            have hnone : fr0.decls x = none := h.typeFresh fr0 (by simp [hsc])
            simp at hb
          have hbOld : fr0.decls x' = some (.ref τ') := by
            simpa [hx'] using hb
          have hdeclOld : typeFrameDeclRef Γ 0 x' τ' := ⟨fr0, by simp [hsc], hbOld⟩
          rcases h.concrete.refDeclRealized hdeclOld with ⟨a, hrefOld, hliveOld⟩
          have hrefNew := runtimeFrameBindsRef_declareObjectState_forward_of_topFresh
            (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hrefOld
          have hane : a ≠ σ.next :=
            heapLiveTypedAt_ne_next_of_nextFresh (σ := σ) (a := a) (τ := τ') h.concrete.nextFresh hliveOld
          have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
            (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
          exact ⟨a, hrefNew, hliveNew⟩
  | succ k =>
      have hkOld : Γ.scopes[k.succ]? = some Γfr' := by
        rwa [scopes_declareTypeObject_succ_iff] at hk
      have hdeclOld : typeFrameDeclRef Γ k.succ x' τ' := ⟨Γfr', hkOld, hb⟩
      rcases h.concrete.refDeclRealized hdeclOld with ⟨a, hrefOld, hliveOld⟩
      have hrefNew := runtimeFrameBindsRef_declareObjectState_forward_of_topFresh
        (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hrefOld
      have hane : a ≠ σ.next :=
        heapLiveTypedAt_ne_next_of_nextFresh (σ := σ) (a := a) (τ := τ') h.concrete.nextFresh hliveOld
      have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
        (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
      exact ⟨a, hrefNew, hliveNew⟩
end DeclareObjectReadyStrong

namespace DeclareRefReadyStrong

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
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases k with
  | zero =>
      cases hsc : Γ.scopes with
      | nil =>
          simp [hsc] at hΓ0
      | cons fr0 frs =>
          simp [declareTypeRef, insertTopDecl, hsc] at hk
          subst Γfr'
          have hx' : x' ≠ x := by
            intro hEq
            subst x'
            have hnone : fr0.decls x = none := h.typeFresh fr0 (by simp [hsc])
            simp at hb
          have hbOld : fr0.decls x' = some (.object τ') := by
            simpa [hx'] using hb
          have hdeclOld : typeFrameDeclObject Γ 0 x' τ' := ⟨fr0, by simp [hsc], hbOld⟩
          rcases h.concrete.objectDeclRealized hdeclOld with ⟨addr, hobjOld, hownOld, hliveOld⟩
          have hobjNew := runtimeFrameBindsObject_declareRefState_forward_of_topFresh
            (σ := σ) (τ := τ) (x := x) (a := a) (h.topFrameFresh hΓ0) hobjOld
          have hownNew := (runtimeFrameOwnsAddress_declareRefState_iff
            (σ := σ) (τ := τ) (x := x) (a := a) (k := 0) (addr := addr)).2 hownOld
          have hliveNew := (heapLiveTypedAt_declareRefState_iff
            (σ := σ) (τ := τ) (x := x) (r := a) (a := addr) (υ := τ')).2 hliveOld
          exact ⟨addr, hobjNew, hownNew, hliveNew⟩
  | succ k =>
      have hkOld : Γ.scopes[k.succ]? = some Γfr' := by
        rwa [scopes_declareTypeRef_succ_iff] at hk
      have hdeclOld : typeFrameDeclObject Γ k.succ x' τ' := ⟨Γfr', hkOld, hb⟩
      rcases h.concrete.objectDeclRealized hdeclOld with ⟨addr, hobjOld, hownOld, hliveOld⟩
      have hobjNew := runtimeFrameBindsObject_declareRefState_forward_of_topFresh
        (σ := σ) (τ := τ) (x := x) (a := a) (h.topFrameFresh hΓ0) hobjOld
      have hownNew := (runtimeFrameOwnsAddress_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (a := a) (k := k.succ) (addr := addr)).2 hownOld
      have hliveNew := (heapLiveTypedAt_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (r := a) (a := addr) (υ := τ')).2 hliveOld
      exact ⟨addr, hobjNew, hownNew, hliveNew⟩

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
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases k with
  | zero =>
      cases hsc : Γ.scopes with
      | nil =>
          simp [hsc] at hΓ0
      | cons fr0 frs =>
          simp [declareTypeRef, insertTopDecl, hsc] at hk
          subst Γfr'
          by_cases hx' : x' = x
          · subst x'
            have hτ' : τ' = τ := by
              have : some (DeclInfo.ref τ) = some (DeclInfo.ref τ') := by
                simpa using hb
              injection this with h_decl_eq
              injection h_decl_eq with h_type_eq
              exact h_type_eq.symm
            subst τ'
            have hkσ0 : ∃ fr, (declareRefState σ τ x a).scopes[0]? = some fr := by
              cases hσ : σ.scopes <;>
                simp [declareRefState, bindTopBinding, hσ]
            rcases hkσ0 with ⟨frσ0, hkσ0⟩
            have hrefNew : runtimeFrameBindsRef (declareRefState σ τ x a) 0 x τ a :=
              runtimeFrameBindsRef_declareRefState_zero_new
                (σ := σ) (τ := τ) (x := x) (a := a) hkσ0
            refine ⟨a, hrefNew, ?_⟩
            exact (heapLiveTypedAt_declareRefState_iff
              (σ := σ) (τ := τ) (x := x) (r := a) (a := a) (υ := τ)).2 haLive
          · have hbOld : fr0.decls x' = some (.ref τ') := by
              simpa [hx'] using hb
            have hdeclOld : typeFrameDeclRef Γ 0 x' τ' := ⟨fr0, by simp [hsc], hbOld⟩
            rcases h.concrete.refDeclRealized hdeclOld with ⟨addr, hrefOld, hliveOld⟩
            have hrefNew := runtimeFrameBindsRef_declareRefState_forward_of_topFresh
              (σ := σ) (τ := τ) (x := x) (a := a) (h.topFrameFresh hΓ0) hrefOld
            have hliveNew := (heapLiveTypedAt_declareRefState_iff
              (σ := σ) (τ := τ) (x := x) (r := a) (a := addr) (υ := τ')).2 hliveOld
            exact ⟨addr, hrefNew, hliveNew⟩
  | succ k =>
      have hkOld : Γ.scopes[k.succ]? = some Γfr' := by
        rwa [scopes_declareTypeRef_succ_iff] at hk
      have hdeclOld : typeFrameDeclRef Γ k.succ x' τ' := ⟨Γfr', hkOld, hb⟩
      rcases h.concrete.refDeclRealized hdeclOld with ⟨addr, hrefOld, hliveOld⟩
      have hrefNew := runtimeFrameBindsRef_declareRefState_forward_of_topFresh
        (σ := σ) (τ := τ) (x := x) (a := a) (h.topFrameFresh hΓ0) hrefOld
      have hliveNew := (heapLiveTypedAt_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (r := a) (a := addr) (υ := τ')).2 hliveOld
      exact ⟨addr, hrefNew, hliveNew⟩
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
    (DeclareObjectReadyStrong.declare_new_object_realization_after_declareObjectState
      (σ := σ) (x := x) (τ := τ) (ov := ov))
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
