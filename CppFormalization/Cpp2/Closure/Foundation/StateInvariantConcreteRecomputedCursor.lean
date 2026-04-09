import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteStrengthening
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCore
import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteRecomputedCursor

Foundation consumes a lower-layer object-core update and adds the closure-side
cursor admissibility witness.

What moved out:
- `declareObjectStateCore`
- `declareObjectStateWithNext`
- plain state-algebra lemmas for scopes/heap/lookup

What remains here:
- admissibility of the chosen post-core cursor relative to closure/state invariants
- the ready package used by object-side transport/full assembly
-/

/--
Chosen post-core cursor, now attached to the post-core state.

It must be:
- fresh against owned/local addresses and heap occupancy
- not a runtime ref target
- monotone relative to the pre-state cursor
-/
structure RecomputedNextWitness (σ : State) : Type where
  addr : Nat
  freshOwned : freshAddrAgainstOwned σ addr
  notRuntimeRefTarget :
    ∀ {k : Nat} {x : Ident} {τ : CppType},
      ¬ runtimeFrameBindsRef σ k x τ addr
  monotone : σ.next ≤ addr

namespace RecomputedNextWitness

@[simp] theorem nextFresh_after_setNext
    {σ : State} (w : RecomputedNextWitness σ) :
    nextFreshAgainstOwned (setNext σ w.addr) := by
  exact w.freshOwned

@[simp] theorem next_notRuntimeRefTarget_after_setNext
    {σ : State} (w : RecomputedNextWitness σ) :
    ∀ {k : Nat} {x : Ident} {τ : CppType},
      ¬ runtimeFrameBindsRef (setNext σ w.addr) k x τ (setNext σ w.addr).next := by
  intro k x τ href
  exact w.notRuntimeRefTarget (by simpa [setNext] using href)

end RecomputedNextWitness

section RecomputedObjectState

/--
Object declaration with an admissible recomputed cursor inherits post-state
freshness directly from the witness.
-/
@[simp] theorem nextFreshAgainstOwned_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    nextFreshAgainstOwned (declareObjectStateWithNext σ τ x ov w.addr) := by
  simpa [declareObjectStateWithNext, setNext] using
    (RecomputedNextWitness.nextFresh_after_setNext (σ := declareObjectStateCore σ τ x ov) w)

/--
Object declaration with an admissible recomputed cursor keeps the chosen cursor
away from runtime ref targets.
-/
@[simp] theorem next_notRuntimeRefTarget_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef
          (declareObjectStateWithNext σ τ x ov w.addr)
          k y υ
          (declareObjectStateWithNext σ τ x ov w.addr).next := by
  -- 変数を導入
  intro k y υ
  -- 定義を展開して整理し、用意された補題を適用
  simpa [declareObjectStateWithNext, setNext] using
    w.next_notRuntimeRefTarget_after_setNext

@[simp] theorem monotone_next_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    (declareObjectStateCore σ τ x ov).next ≤
      (declareObjectStateWithNext σ τ x ov w.addr).next := by
  simpa [declareObjectStateWithNext, setNext, next_declareObjectStateCore] using w.monotone

end RecomputedObjectState

/--
Ready package for object declaration under the recomputed-cursor policy.

This remains in Foundation because it depends on `DeclareObjectReadyStrong`,
which is already a closure/foundation-side notion.

In addition to structural/cursor readiness, the package also carries
initializer compatibility with the declared object type.
-/

def IsValueCompatible (ov : Option Value) (τ : CppType) : Prop :=
  match ov with
  | none => True
  | some v => ValueCompat v τ

@[simp] theorem isValueCompatible_none
    {τ : CppType} :
    IsValueCompatible none τ := by
  simp [IsValueCompatible]

@[simp] theorem isValueCompatible_some
    {v : Value} {τ : CppType} :
    IsValueCompatible (some v) τ ↔ ValueCompat v τ := by
  simp [IsValueCompatible]

structure DeclareObjectReadyRecomputed
    (Γ : TypeEnv) (σ : State) (x : Ident)
    (τ : CppType) (ov : Option Value) : Type where
  ready : DeclareObjectReadyStrong Γ σ x
  cursor : RecomputedNextWitness (declareObjectStateCore σ τ x ov)
  initCompat : IsValueCompatible ov τ

namespace DeclareObjectReadyRecomputed

@[simp] theorem initCompat_after
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    IsValueCompatible ov τ :=
  h.initCompat



@[simp] theorem nextFresh_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    nextFreshAgainstOwned (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  exact nextFreshAgainstOwned_declareObjectStateWithNext h.cursor

@[simp] theorem next_not_ref_target_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef
          (declareObjectStateWithNext σ τ x ov h.cursor.addr)
          k y υ
          (declareObjectStateWithNext σ τ x ov h.cursor.addr).next := by
  exact next_notRuntimeRefTarget_declareObjectStateWithNext h.cursor

@[simp] theorem monotone_next
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    (declareObjectStateCore σ τ x ov).next ≤
      (declareObjectStateWithNext σ τ x ov h.cursor.addr).next := by
  exact monotone_next_declareObjectStateWithNext h.cursor

end DeclareObjectReadyRecomputed


section SemanticsBridge

private theorem currentScopeFresh_of_ready
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
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

namespace DeclareObjectReadyRecomputed

@[simp] theorem declaresObjectWithNext_after
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hobj : ObjectType τ) :
    DeclaresObjectWithNext σ τ x ov h.cursor.addr
      (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  refine ⟨hobj, ?_, ?_, h.initCompat, rfl⟩
  · exact currentScopeFresh_of_ready h.ready hΓ0
  · exact h.ready.concrete.nextFresh.1

@[simp] theorem declaresObject_after
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hobj : ObjectType τ) :
    DeclaresObject σ τ x ov
      (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  exact ⟨h.cursor.addr, h.declaresObjectWithNext_after hΓ0 hobj⟩

@[simp] theorem bigStepDeclareObjNone
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hobj : ObjectType τ) :
    BigStepStmt σ (.declareObj τ x none) .normal
      (declareObjectStateWithNext σ τ x none h.cursor.addr) := by
  exact BigStepStmt.declareObjNone (h.declaresObject_after hΓ0 hobj)

@[simp] theorem bigStepDeclareObjSome
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {e : ValExpr} {v : Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ (some v))
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hval : BigStepValue σ e v)
    (hobj : ObjectType τ) :
    BigStepStmt σ (.declareObj τ x (some e)) .normal
      (declareObjectStateWithNext σ τ x (some v) h.cursor.addr) := by
  exact BigStepStmt.declareObjSome hval (h.declaresObject_after hΓ0 hobj)

end DeclareObjectReadyRecomputed

end SemanticsBridge

end Cpp
