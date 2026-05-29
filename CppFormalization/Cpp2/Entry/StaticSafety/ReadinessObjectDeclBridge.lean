import CppFormalization.Cpp2.Operational.Expr

namespace Cpp

/-!
# CppFormalization.Cpp2.Static.Safety.ReadinessObjectDeclBridge

Pure safety-side payload for object-declaration initializer storage.

This file intentionally contains no Closure imports.  It records the
runtime/safety relation between an optional initializer expression and the
optional value stored into the declared object.
-/

/--
object declaration の initializer が、最終的に object に格納される初期値 `ov`
を与えることを表す runtime-side relation.

現在の idealized concrete semantics では、`some e` の場合は
「`e` が値 `v` へ評価され、その `v` が `τ` に compatible である」ことをもって
「object に格納される値が `some v` である」とみなす。
-/
structure ObjectDeclInitStoredValueSome
    (σ : State) (τ : CppType) (e : ValExpr) (v : Value) : Type where
  initializerEvaluatesTo : BigStepValue σ e v
  storedValueCompat      : ValueCompat v τ

/-
  inductive ではなく def (関数) として定義。
  引数の形によって、返すべき「証拠の型」を計算する。
-/
def ObjectDeclInitStoredValue
    (σ : State) (τ : CppType) :
    Option ValExpr → Option Value → Type
  | none,   none   => PUnit
  | some e, some v => ObjectDeclInitStoredValueSome σ τ e v
  | _,      _      => PEmpty

namespace ObjectDeclInitStoredValue

section Forward

variable {σ : State} {τ : CppType}

/-- (A1) initializer なし・stored value なしの構築。 -/
def intro_none :
    ObjectDeclInitStoredValue σ τ none none :=
  PUnit.unit

/-- (A2) initializer あり・stored value ありの構築。 -/
def intro_some
    {e : ValExpr} {v : Value}
    (hEval   : BigStepValue σ e v)
    (hCompat : ValueCompat v τ) :
    ObjectDeclInitStoredValue σ τ (some e) (some v) :=
  ⟨hEval, hCompat⟩

end Forward

section Elimination

variable {σ : State} {τ : CppType}

/-- (B1) `some/some` 証拠の分解。field projection を直接使う。 -/
theorem some_cases
    {e : ValExpr} {v : Value}
    (h : ObjectDeclInitStoredValue σ τ (some e) (some v)) :
    BigStepValue σ e v ∧ ValueCompat v τ := by
  exact ⟨h.initializerEvaluatesTo, h.storedValueCompat⟩

/-- (B2) `none/none` の inhabitant は自明に `PUnit.unit`。 -/
theorem none_cases
    (h : ObjectDeclInitStoredValue σ τ none none) :
    h = PUnit.unit := by
  cases h
  rfl

end Elimination

section Impossible

variable {σ : State} {τ : CppType}

/-- (C1) initializer が無いのに stored value があるのは不可能。 -/
theorem none_some_impossible
    {v : Value}
    (h : ObjectDeclInitStoredValue σ τ none (some v)) :
    False := by
  nomatch h

/-- (C2) initializer があるのに stored value が無いのは不可能。 -/
theorem some_none_impossible
    {e : ValExpr}
    (h : ObjectDeclInitStoredValue σ τ (some e) none) :
    False := by
  nomatch h

/-- (C3) `none` 側なら `ov` は必ず `none`。 -/
theorem ov_eq_none_of_none
    {ov : Option Value}
    (h : ObjectDeclInitStoredValue σ τ none ov) :
    ov = none := by
  cases ov with
  | none =>
      rfl
  | some v =>
      exact False.elim (none_some_impossible h)

/-- (C4) `some e` 側なら `ov` は必ず `some v` の形。 -/
theorem exists_value_of_some
    {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclInitStoredValue σ τ (some e) ov) :
    ∃ v, ov = some v := by
  cases ov with
  | none =>
      exact False.elim (some_none_impossible h)
  | some v =>
      exact ⟨v, rfl⟩

end Impossible

@[simp] theorem ov_eq_none
    {σ : State} {τ : CppType} {ov : Option Value}
    (h : ObjectDeclInitStoredValue σ τ none ov) :
    ov = none :=
  ov_eq_none_of_none h

theorem ov_is_some_of_some
    {σ : State} {τ : CppType} {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclInitStoredValue σ τ (some e) ov) :
    ∃ v, ov = some v :=
  exists_value_of_some h

def witness
    {σ : State} {τ : CppType} {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclInitStoredValue σ τ (some e) ov) :
    {v : Value // ov = some v ∧ BigStepValue σ e v ∧ ValueCompat v τ} := by
  cases hov : ov with
  | none =>
      subst hov
      nomatch h
  | some v =>
      subst hov
      exact ⟨v, rfl, h.initializerEvaluatesTo, h.storedValueCompat⟩

@[simp] theorem nonempty_none_iff
    {σ : State} {τ : CppType} {ov : Option Value} :
    Nonempty (ObjectDeclInitStoredValue σ τ none ov) ↔ ov = none := by
  constructor
  · rintro ⟨h⟩
    exact ov_eq_none_of_none h
  · intro hov
    subst hov
    exact ⟨intro_none⟩

@[simp] theorem nonempty_some_iff
    {σ : State} {τ : CppType} {e : ValExpr} {ov : Option Value} :
    Nonempty (ObjectDeclInitStoredValue σ τ (some e) ov) ↔
      ∃ v, ov = some v ∧ BigStepValue σ e v ∧ ValueCompat v τ := by
  constructor
  · rintro ⟨h⟩
    cases hov : ov with
    | none =>
      subst hov
      nomatch h
    | some v =>
        subst hov
        exact ⟨v, rfl, h.initializerEvaluatesTo, h.storedValueCompat⟩
  · rintro ⟨v, hov, hstep, hcompat⟩
    subst hov
    exact ⟨intro_some hstep hcompat⟩

end ObjectDeclInitStoredValue

end Cpp
