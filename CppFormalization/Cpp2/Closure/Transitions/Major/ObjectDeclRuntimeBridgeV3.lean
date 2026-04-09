import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.Foundation.ReadinessObjectDeclBridge

namespace Cpp

/-!
# Closure.External.ObjectDeclRuntimeBridgeV3

Thin theorem-backed runtime builders for object-declaration statements.

Purpose:
- keep `RuntimePiecesV3` construction out of ad hoc toy instances,
- expose a reusable conversion from `BodyDynamicBoundary` to `RuntimePiecesV3`,
- give canonical runtime-package builders from the recomputed-cursor
  object-declaration ready package.

This is intentionally runtime-side only: it does not choose reflection data,
adequacy, or a ready assembly.
-/

namespace BodyDynamicBoundary

/-- Any dynamic boundary canonically determines the runtime package expected by
`VerifiedStdFragmentV3`. -/
@[simp] def toRuntimePiecesV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyDynamicBoundary Γ σ st) :
    RuntimePiecesV3 Γ σ st :=
  { dynamic := h }

@[simp] theorem toRuntimePiecesV3_dynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyDynamicBoundary Γ σ st) :
    h.toRuntimePiecesV3.dynamic = h := rfl

end BodyDynamicBoundary

namespace DeclareObjectReadyRecomputed

/-- Runtime package for a declaration without initializer expression. -/
@[simp] def runtimePieces_declareObjNone
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    (hobj : ObjectType τ) :
    RuntimePiecesV3 Γ σ (.declareObj τ x none) :=
  (bodyDynamicBoundary_declareObjNone (h := h) hobj).toRuntimePiecesV3

@[simp] theorem runtimePieces_declareObjNone_dynamic
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    (hobj : ObjectType τ) :
    (runtimePieces_declareObjNone (h := h) hobj).dynamic =
      bodyDynamicBoundary_declareObjNone (h := h) hobj := rfl

/-- Runtime package for a declaration with initializer expression.  The
recomputed ready package supplies the state-side prerequisites, while the
initializer contributes the expression-side runtime assumptions. -/
@[simp] def runtimePieces_declareObjSome
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {ov : Option Value} {e : ValExpr}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hobj : ObjectType τ)
    (hty : HasValueType Γ e τ)
    (hre : ExprReadyConcrete Γ σ e τ) :
    RuntimePiecesV3 Γ σ (.declareObj τ x (some e)) :=
  (bodyDynamicBoundary_declareObjSome (h := h) hobj hty hre).toRuntimePiecesV3

@[simp] theorem runtimePieces_declareObjSome_dynamic
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {ov : Option Value} {e : ValExpr}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hobj : ObjectType τ)
    (hty : HasValueType Γ e τ)
    (hre : ExprReadyConcrete Γ σ e τ) :
    (runtimePieces_declareObjSome (h := h) hobj hty hre).dynamic =
      bodyDynamicBoundary_declareObjSome (h := h) hobj hty hre := rfl

/-- Expose the underlying concrete state carried by the runtime package for a
non-initialized declaration.  This is often the only part needed by later
package assembly proofs. -/
@[simp] theorem runtimePieces_declareObjNone_state
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    (h : DeclareObjectReadyRecomputed Γ σ x τ none)
    (hobj : ObjectType τ) :
    (runtimePieces_declareObjNone (h := h) hobj).dynamic.state = h.ready.concrete := rfl

/-- The runtime package for an initialized declaration also carries the same
concrete pre-state; only the statement-side readiness differs. -/
@[simp] theorem runtimePieces_declareObjSome_state
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {ov : Option Value} {e : ValExpr}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hobj : ObjectType τ)
    (hty : HasValueType Γ e τ)
    (hre : ExprReadyConcrete Γ σ e τ) :
    (runtimePieces_declareObjSome (h := h) hobj hty hre).dynamic.state = h.ready.concrete := rfl

end DeclareObjectReadyRecomputed

end Cpp
