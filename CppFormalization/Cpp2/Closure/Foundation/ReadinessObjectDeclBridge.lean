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
def ObjectDeclInitStoredValue
    (σ : State) (τ : CppType)
    (initExpr : Option ValExpr) (ov : Option Value) : Prop :=
  match initExpr with
  | none => ov = none
  | some e =>
      ∃ v,
        ov = some v ∧
        BigStepValue σ e v ∧
        ValueCompat v τ

namespace ObjectDeclInitStoredValue

@[simp] theorem none_iff
     {σ : State} {τ : CppType} {ov : Option Value} :
    ObjectDeclInitStoredValue  σ τ none ov ↔ ov = none :=
  Iff.rfl

@[simp] theorem some_iff
     {σ : State} {τ : CppType} {e : ValExpr} {ov : Option Value} :
    ObjectDeclInitStoredValue  σ τ (some e) ov ↔
      ∃ v, ov = some v ∧ BigStepValue σ e v ∧ ValueCompat v τ :=
  Iff.rfl

@[simp] theorem ov_eq_none
    {σ : State} {τ : CppType} {ov : Option Value}
    (h : ObjectDeclInitStoredValue  σ τ none ov) :
    ov = none := h

@[simp] theorem exists_value_of_some
    {σ : State} {τ : CppType} {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclInitStoredValue  σ τ (some e) ov) :
    ∃ v, ov = some v ∧ BigStepValue σ e v ∧ ValueCompat v τ := h

end ObjectDeclInitStoredValue

namespace DeclareObjectReadyRecomputed

@[simp] theorem stmtReadyConcrete_declareObjNone
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    (hobj : ObjectType τ) :
    StmtReadyConcrete Γ σ (.declareObj τ x none) := by
  exact .declareObjNone h.scopeFresh hobj

@[simp] theorem stmtReadyConcrete_declareObjSome
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {ov : Option Value} {e : ValExpr}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hobj : ObjectType τ)
    (hty : HasValueType Γ e τ)
    (hre : ExprReadyConcrete Γ σ e τ) :
    StmtReadyConcrete Γ σ (.declareObj τ x (some e)) := by
  exact .declareObjSome h.scopeFresh hobj hty hre

@[simp] theorem bodyDynamicBoundary_declareObjNone
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    (hobj : ObjectType τ) :
    BodyDynamicBoundary Γ σ (.declareObj τ x none) := by
  exact ⟨h.ready.concrete, h.stmtReadyConcrete_declareObjNone hobj⟩

@[simp] theorem bodyDynamicBoundary_declareObjSome
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {ov : Option Value} {e : ValExpr}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hobj : ObjectType τ)
    (hty : HasValueType Γ e τ)
    (hre : ExprReadyConcrete Γ σ e τ) :
    BodyDynamicBoundary Γ σ (.declareObj τ x (some e)) := by
  exact ⟨h.ready.concrete, h.stmtReadyConcrete_declareObjSome hobj hty hre⟩

end DeclareObjectReadyRecomputed

end Cpp
