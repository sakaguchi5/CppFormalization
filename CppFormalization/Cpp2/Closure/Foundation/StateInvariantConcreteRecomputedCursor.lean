import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteStrengthening
import CppFormalization.Cpp2.Core.RuntimeObjectCore
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext
import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

/-!
Recomputed-cursor object declaration package.

Canonical naming freshness for declaration readiness is `currentTypeScopeFresh`.
Frame-local freshness remains an internal support notion inside Foundation,
but the exported ready package carries the scope-level predicate explicitly.
-/

namespace RecomputedObjectState

structure RecomputedNextWitness (σ : State) : Type where
  addr : Nat
  freshOwned : freshAddrAgainstOwned σ addr
  notRuntimeRefTarget :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef σ k y υ addr
  monotone : σ.next ≤ addr

@[simp] theorem nextFreshAgainstOwned_after_setNext
    {σ : State} (w : RecomputedNextWitness σ) :
    nextFreshAgainstOwned (setNext σ w.addr) := by
  refine ⟨?_, ?_⟩
  · simpa [setNext] using w.freshOwned.1
  · intro k fr hk
    simpa [setNext] using w.freshOwned.2 k fr hk

@[simp] theorem next_notRuntimeRefTarget_after_setNext
    {σ : State} (w : RecomputedNextWitness σ) :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef (setNext σ w.addr) k y υ (setNext σ w.addr).next := by
  intro k y υ
  simpa [setNext] using (w.notRuntimeRefTarget (k := k) (y := y) (υ := υ))

@[simp] theorem nextFreshAgainstOwned_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    nextFreshAgainstOwned (declareObjectStateWithNext σ τ x ov w.addr) := by
  simp [declareObjectStateWithNext,nextFreshAgainstOwned_after_setNext]

@[simp] theorem next_notRuntimeRefTarget_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov w.addr) k y υ
          (declareObjectStateWithNext σ τ x ov w.addr).next := by
  intro k y υ
  -- w.フィールド名 ではなく 定理名 w で呼び出す
  simpa [declareObjectStateWithNext] using
    (next_notRuntimeRefTarget_after_setNext w)

@[simp] theorem monotone_next_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    (declareObjectStateCore σ τ x ov).next ≤
      (declareObjectStateWithNext σ τ x ov w.addr).next := by
  simpa [declareObjectStateWithNext, setNext] using w.monotone

end RecomputedObjectState

open RecomputedObjectState

/-- Initializer compatibility used by the recomputed object-declaration package. -/
def IsValueCompatible (ov : Option Value) (τ : CppType) : Prop :=
  match ov with
  | none => True
  | some v => ValueCompat v τ

@[simp] theorem isValueCompatible_none {τ : CppType} : IsValueCompatible none τ := by
  simp [IsValueCompatible]

@[simp] theorem isValueCompatible_some {v : Value} {τ : CppType} :
    IsValueCompatible (some v) τ ↔ ValueCompat v τ := by
  simp [IsValueCompatible]

/--
Ready package for object declaration under the recomputed-cursor policy.

`currentTypeScopeFresh` is the exported, canonical naming predicate.
The stronger frame-local data stays inside `DeclareObjectReadyStrong`.
-/
structure DeclareObjectReadyRecomputed
    (Γ : TypeEnv) (σ : State) (x : Ident) (τ : CppType) (ov : Option Value) : Type where
  ready : DeclareObjectReadyStrong Γ σ x
  scopeFresh : currentTypeScopeFresh Γ x
  cursor : RecomputedNextWitness (declareObjectStateCore σ τ x ov)
  initCompat : IsValueCompatible ov τ

namespace DeclareObjectReadyRecomputed

@[simp] theorem typeScopeFresh_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    currentTypeScopeFresh Γ x := h.scopeFresh

@[simp] theorem initCompat_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) : IsValueCompatible ov τ := h.initCompat

@[simp] theorem nextFresh_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    nextFreshAgainstOwned (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  exact nextFreshAgainstOwned_declareObjectStateWithNext h.cursor

@[simp] theorem next_not_ref_target_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov h.cursor.addr) k y υ
          (declareObjectStateWithNext σ τ x ov h.cursor.addr).next := by
  intro k y υ
  exact next_notRuntimeRefTarget_declareObjectStateWithNext h.cursor

@[simp] theorem monotone_next
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    (declareObjectStateCore σ τ x ov).next ≤
      (declareObjectStateWithNext σ τ x ov h.cursor.addr).next := by
  exact monotone_next_declareObjectStateWithNext h.cursor

private theorem currentScopeFresh_of_ready
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame} (hΓ0 : Γ.scopes[0]? = some Γfr) :
    currentScopeFresh σ x := by
  cases hσ : σ.scopes with
  | nil =>
      have hlen : Γ.scopes.length = 0 := by
        simpa [frameDepthAgreement, hσ] using h.concrete.frameDepth
      cases hG : Γ.scopes with
      | nil => simp [hG] at hΓ0
      | cons fr frs => simp [hG] at hlen
  | cons fr frs =>
      simpa [currentScopeFresh, hσ] using (h.topFrameFresh hΓ0) fr (by simp [hσ])

@[simp] theorem declaresObjectWithNext_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    {Γfr : TypeFrame} (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hobj : ObjectType τ) :
    DeclaresObjectWithNext σ τ x ov h.cursor.addr
      (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  refine ⟨declareObjectStateCore σ τ x ov, ?_, ?_⟩
  · refine ⟨hobj, ?_, ?_, h.initCompat, rfl⟩
    · exact currentScopeFresh_of_ready h.ready hΓ0
    · exact h.ready.concrete.nextFresh.1
  · refine ⟨?_, rfl⟩
    simpa [FreshPostCursor, freshAddrAgainstOwned] using h.cursor.freshOwned

@[simp] theorem declaresObject_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    {Γfr : TypeFrame} (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hobj : ObjectType τ) :
    DeclaresObject σ τ x ov
      (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  exact ⟨h.cursor.addr, h.declaresObjectWithNext_after hΓ0 hobj⟩

end DeclareObjectReadyRecomputed

end Cpp
