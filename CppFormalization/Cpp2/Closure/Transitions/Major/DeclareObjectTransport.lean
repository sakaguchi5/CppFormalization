import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext

namespace Cpp
namespace DeclareObjectTransport

/-!
# Closure.Transitions.Major.DeclareObjectTransport

`declareObjectStateWithNext` が runtime witness をどう運ぶかだけをまとめた補助層。
ここでは `ScopedTypedStateConcrete` の final assembly には触れず、
top-frame 更新に伴う binding / ownership / live witness の transport だけを切り出す。
-/

theorem runtimeFrameBindsRef_zero_preserved_of_ne_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hy : y ≠ x)
    (hbind : runtimeFrameBindsRef σ 0 y υ a) :
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) 0 y υ a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hbind with ⟨fr0, hk0, hb0⟩
  have hfr0 : fr0 = fr := by
    simpa [hsc] using hk0.symm
  subst fr0
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew, hy, hb0]

theorem runtimeFrameBindsRef_succ_preserved_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {j a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsRef σ (j + 1) y υ a) :
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a := by
  rcases hbind with ⟨fr0, hk0, hb0⟩
  exact ⟨fr0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb0⟩

theorem runtimeFrameBindsRef_succ_declareObjectStateWithNext_inv
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {j a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a) :
    runtimeFrameBindsRef σ (j + 1) y υ a := by
  rcases hbind with ⟨fr0, hk0, hb0⟩
  exact ⟨fr0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb0⟩

theorem heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {a : Nat} {υ : CppType} :
    a ≠ σ.next →
    heapLiveTypedAt σ a υ →
    heapLiveTypedAt (declareObjectStateWithNext σ τ x ov aNext) a υ := by
  intro ha hlive
  rcases hlive with ⟨c, hheap, hty, halive⟩
  refine ⟨c, ?_, hty, halive⟩
  simpa using
    (RuntimeObjectCoreWithNext.heap_declareObjectStateWithNext_other
      (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext) (a := a) ha).trans hheap

theorem runtimeFrameOwnsAddress_zero_declareObjectStateWithNext_cases
    {σ : State} {aNext : Nat} {x : Ident} {τ : CppType} {ov : Option Value}
    {fr : ScopeFrame} {frs : List ScopeFrame} {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 a) :
    a = σ.next ∨ runtimeFrameOwnsAddress σ 0 a := by
  let frNew : ScopeFrame :=
    { binds := fun y => if y = x then some (.object τ σ.next) else fr.binds y,
      locals := σ.next :: fr.locals }
  rcases hown with ⟨fr', hk, hmem⟩
  have hfr' : fr' = frNew := by
    simpa [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc] using hk.symm
  subst fr'
  simp [frNew] at hmem
  rcases hmem with hnew | hold
  · exact Or.inl hnew
  · exact Or.inr ⟨fr, by simp [hsc], hold⟩

theorem runtimeFrameOwnsAddress_succ_declareObjectStateWithNext_inv
    {σ : State} {aNext : Nat} {x : Ident} {τ : CppType} {ov : Option Value}
    {fr : ScopeFrame} {frs : List ScopeFrame} {j a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) (j + 1) a) :
    runtimeFrameOwnsAddress σ (j + 1) a := by
  rcases hown with ⟨fr', hk, hmem⟩
  exact ⟨fr',
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk,
    hmem⟩

theorem runtimeFrameBindsObject_zero_new_declareObjectStateWithNext
    {σ : State} {aNext : Nat} {x : Ident} {τ : CppType} {ov : Option Value}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs) :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 x τ σ.next := by
  let frNew : ScopeFrame :=
    { binds := fun y => if y = x then some (.object τ σ.next) else fr.binds y,
      locals := σ.next :: fr.locals }
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew]

theorem runtimeFrameBindsObject_zero_preserved_of_ne_declareObjectStateWithNext
    {σ : State} {aNext : Nat} {x y : Ident} {τ υ : CppType} {ov : Option Value} {a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hy : y ≠ x)
    (hbind : runtimeFrameBindsObject σ 0 y υ a) :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 y υ a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hbind with ⟨fr0, hk0, hb0⟩
  have hfr0 : fr0 = fr := by
    simpa [hsc] using hk0.symm
  subst fr0
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew, hy, hb0]

theorem runtimeFrameBindsObject_succ_preserved_declareObjectStateWithNext
    {σ : State} {aNext : Nat} {x y : Ident} {τ υ : CppType} {ov : Option Value} {j a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsObject σ (j + 1) y υ a) :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a := by
  rcases hbind with ⟨fr0, hk0, hb0⟩
  exact ⟨fr0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb0⟩

theorem runtimeFrameBindsObject_zero_declareObjectStateWithNext_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {y : Ident} {υ : CppType} {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 y υ a) :
    (y = x ∧ υ = τ ∧ a = σ.next) ∨ runtimeFrameBindsObject σ 0 y υ a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hbind with ⟨fr', hk, hb⟩
  have hfr' : fr' = frNew := by
    simpa [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc] using hk.symm
  subst fr'
  by_cases hy : y = x
  · subst hy
    left
    have hobj : (Binding.object τ σ.next) = (.object υ a) := by
      simpa [frNew] using hb
    cases hobj
    exact ⟨rfl, rfl, rfl⟩
  · right
    refine ⟨fr, by simp [hsc], ?_⟩
    simpa [frNew, hy] using hb

theorem runtimeFrameBindsObject_succ_declareObjectStateWithNext_inv
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {j : Nat} {y : Ident} {υ : CppType} {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a) :
    runtimeFrameBindsObject σ (j + 1) y υ a := by
  rcases hbind with ⟨fr', hk, hb⟩
  exact ⟨fr',
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb⟩

theorem runtimeFrameOwnsAddress_zero_new_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs) :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 σ.next := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew]

theorem runtimeFrameOwnsAddress_zero_preserved_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress σ 0 a) :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hown with ⟨fr0, hk0, hmem0⟩
  have hfr0 : fr0 = fr := by
    simpa [hsc] using hk0.symm
  subst fr0
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew, hmem0]

theorem runtimeFrameOwnsAddress_succ_preserved_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {j a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress σ (j + 1) a) :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) (j + 1) a := by
  rcases hown with ⟨fr', hk, hmem⟩
  exact ⟨fr',
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk,
    hmem⟩

end DeclareObjectTransport
end Cpp
