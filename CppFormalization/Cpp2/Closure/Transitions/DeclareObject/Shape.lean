import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteRecomputedCursor

namespace Cpp

/-!
# Closure.Transitions.DeclareObject.Shape

Shape lemmas for the existential-wrapper object-declaration semantics.

This is the lowest declaration-object transition layer.  It only describes the
logical shape of `DeclaresObject` and its `declareObjectStateWithNext` witness;
it does not import or depend on the final `ScopedTypedStateConcrete` preservation
assembly.
-/

@[simp] theorem declaresObject_exists_withNext_data
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {σ' : State} :
    DeclaresObject σ τ x ov σ' ↔
      ∃ aNext,
        ObjectType τ ∧
        currentScopeFresh σ x ∧
        σ.heap σ.next = none ∧
        IsValueCompatible ov τ ∧
        FreshPostCursor (declareObjectStateCore σ τ x ov) aNext ∧
        σ' = declareObjectStateWithNext σ τ x ov aNext := by
  constructor
  · intro h
    rcases h with ⟨aNext, hwith⟩
    rcases hwith with ⟨σcore, hpayload, hpolicy⟩
    rcases hpayload with ⟨hobj, hfresh, hheap, hcompat, hcore⟩
    rcases hpolicy with ⟨hpost, hσ'⟩
    subst hcore
    subst hσ'
    exact ⟨aNext, hobj, hfresh, hheap, hcompat, hpost, rfl⟩
  · intro h
    rcases h with ⟨aNext, hobj, hfresh, hheap, hcompat, hpost, hσ'⟩
    refine ⟨aNext, ?_⟩
    refine ⟨declareObjectStateCore σ τ x ov, ?_, ?_⟩
    · exact ⟨hobj, hfresh, hheap, hcompat, rfl⟩
    · subst hσ'
      exact ⟨hpost, rfl⟩

theorem declaresObject_exists_withNext_data_weak
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {σ' : State} :
    DeclaresObject σ τ x ov σ' →
      ∃ aNext,
        ObjectType τ ∧
        currentScopeFresh σ x ∧
        σ.heap σ.next = none ∧
        IsValueCompatible ov τ ∧
        σ' = declareObjectStateWithNext σ τ x ov aNext := by
  intro h
  rcases h with ⟨aNext, hwith⟩
  rcases hwith with ⟨σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobj, hfresh, hheap, hcompat, hcore⟩
  rcases hpolicy with ⟨hpost, hσ'⟩
  subst hcore
  subst hσ'
  exact ⟨aNext, hobj, hfresh, hheap, hcompat, rfl⟩

@[simp] theorem declaresObject_exists_withNext_data_strong
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {σ' : State} :
    DeclaresObject σ τ x ov σ' ↔
      ∃ aNext,
        ObjectType τ ∧
        currentScopeFresh σ x ∧
        σ.heap σ.next = none ∧
        IsValueCompatible ov τ ∧
        FreshPostCursor (declareObjectStateCore σ τ x ov) aNext ∧
        σ' = declareObjectStateWithNext σ τ x ov aNext := by
  constructor
  · intro h
    rcases h with ⟨aNext, hwith⟩
    rcases hwith with ⟨σcore, hpayload, hpolicy⟩
    rcases hpayload with ⟨hobj, hfresh, hheap, hcompat, hcore⟩
    rcases hpolicy with ⟨hpost, hσ'⟩
    subst hcore
    subst hσ'
    exact ⟨aNext, hobj, hfresh, hheap, hcompat, hpost, rfl⟩
  · intro h
    rcases h with ⟨aNext, hobj, hfresh, hheap, hcompat, hpost, hσ'⟩
    refine ⟨aNext, ?_⟩
    refine ⟨declareObjectStateCore σ τ x ov, ?_, ?_⟩
    · exact ⟨hobj, hfresh, hheap, hcompat, rfl⟩
    · subst hσ'
      exact ⟨hpost, rfl⟩

@[simp] theorem declaresObject_exists_cursor
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {σ' : State} :
    DeclaresObject σ τ x ov σ' →
      ∃ aNext, σ' = declareObjectStateWithNext σ τ x ov aNext := by
  intro h
  rcases (declaresObject_exists_withNext_data_weak h) with
    ⟨aNext, _hobj, _hfresh, _hheap, _hcompat, hσ'⟩
  exact ⟨aNext, hσ'⟩

/--
Transition-side wrapper: from a recomputed ready package we can produce
an existential object-declaration step whose public naming premise is the
canonical `currentTypeScopeFresh`.
-/
@[simp] theorem declaresObject_of_recomputedReady
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    {Γfr : TypeFrame} (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hobj : ObjectType τ) :
    DeclaresObject σ τ x ov (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  exact h.declaresObject_after hΓ0 hobj

/--
A decomposition shape tailored to the new existential-wrapper semantics.
This is the right entry point for transition proofs that need to peel
`DeclaresObject` before using low-level state lemmas.
-/
theorem declaresObject_cases_withNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {σ' : State}
    (h : DeclaresObject σ τ x ov σ') :
    ∃ aNext,
      ObjectType τ ∧
      currentScopeFresh σ x ∧
      σ.heap σ.next = none ∧
      IsValueCompatible ov τ ∧
      σ' = declareObjectStateWithNext σ τ x ov aNext :=
  declaresObject_exists_withNext_data_weak h

end Cpp
