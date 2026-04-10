import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteRecomputedCursor

namespace Cpp

/-!
# Closure.Foundation.ReadinessObjectDeclBridge

`currentTypeScopeFresh` を公開の正準 fresh predicate として固定したうえで、
recomputed-cursor object-declaration package から `StmtReadyConcrete` /
`BodyDynamicBoundary` へ降りる薄い bridge を与える。

方針:
- `Readiness.lean` 本体には recomputed-cursor policy を埋め込まない。
- bridge は専用ファイルへ分離し、公開面では `currentTypeScopeFresh` だけを使う。
- `DeclareObjectReadyStrong` から無理に `currentTypeScopeFresh` を導かない。
-/

/--
object declaration の initializer が、最終的に object に格納される初期値 `ov`
を与えることを表す runtime-side relation.

現在の idealized concrete semantics では、`some e` の場合は
「`e` が値 `v` へ評価され、その `v` が `τ` に compatible である」ことをもって
「object に格納される値が `some v` である」とみなす。
-/
/-
  inductive ではなく def (関数) として定義。
  引数の形によって、返すべき「証拠の型」を計算する。
-/
structure ObjectDeclInitStoredValueSome
    (σ : State) (τ : CppType) (e : ValExpr) (v : Value) : Type where
  initializerEvaluatesTo : BigStepValue σ e v
  storedValueCompat      : ValueCompat v τ

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
end ObjectDeclInitStoredValue


namespace ObjectDeclInitStoredValue

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

namespace DeclareObjectReadyRecomputed

theorem toStmtReadyConcrete_declareObjNone
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    (hobj : ObjectType τ) :
    StmtReadyConcrete Γ σ (.declareObj τ x none) := by
  exact .declareObjNone h.scopeFresh hobj

theorem toStmtReadyConcrete_declareObjSome
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {ov : Option Value} {e : ValExpr}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hobj : ObjectType τ)
    (hty : HasValueType Γ e τ)
    (hre : ExprReadyConcrete Γ σ e τ) :
    StmtReadyConcrete Γ σ (.declareObj τ x (some e)) := by
  exact .declareObjSome h.scopeFresh hobj hty hre

theorem toBodyDynamicBoundary_declareObjNone
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    (hobj : ObjectType τ) :
    BodyDynamicBoundary Γ σ (.declareObj τ x none) := by
  exact BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
    h.ready.concrete
    (toStmtReadyConcrete_declareObjNone h hobj)

theorem toBodyDynamicBoundary_declareObjSome
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {ov : Option Value} {e : ValExpr}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hobj : ObjectType τ)
    (hty : HasValueType Γ e τ)
    (hre : ExprReadyConcrete Γ σ e τ) :
    BodyDynamicBoundary Γ σ (.declareObj τ x (some e)) := by
  exact BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
    h.ready.concrete
    (toStmtReadyConcrete_declareObjSome h hobj hty hre)

end DeclareObjectReadyRecomputed

end Cpp
