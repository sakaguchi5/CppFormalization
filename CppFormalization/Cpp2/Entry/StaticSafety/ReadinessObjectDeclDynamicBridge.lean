import CppFormalization.Cpp2.Entry.StaticSafety.ReadinessObjectDeclBridge
import CppFormalization.Cpp2.Entry.StaticSafety.BodyDynamicBoundary
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.RecomputedCursor

/-!
# CppFormalization.Cpp2.Static.Safety.ReadinessObjectDeclDynamicBridge

Static/Safety bridge moved from Closure/Foundation.

This file must not depend on Closure.
-/
namespace Cpp

/-!
# CppFormalization.Cpp2.Static.Safety.ReadinessObjectDeclDynamicBridge

Static/Safety-side bridge from recomputed-cursor object-declaration readiness to
`StmtReadyConcrete` / `BodyDynamicBoundary`.

The pure stored-value payload now lives in
`CppFormalization.Cpp2.Static.Safety.ReadinessObjectDeclBridge`.

This file adds the dynamic-boundary-facing bridge layer.
-/

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
