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
