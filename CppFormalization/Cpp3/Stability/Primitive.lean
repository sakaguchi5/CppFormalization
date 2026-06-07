import CppFormalization.Cpp3.Stability.Expr

/-!
# CppFormalization.Cpp3.Stability.Primitive

Stability packages for primitive execution boundaries.

A primitive boundary already contains the operational step and its post-state.
This file records the visible stability proposition associated with that
post-state; it still does not decide which continuation should consume it.
-/

namespace Cpp3
namespace Stability

/-- Assignment execution leaves a certified stable post-state surface. -/
structure AssignBoundaryStability
    (Γ : TypeEnv) (σ σ₁ : State) (a : CppAssign) : Type where
  boundary : Boundary.AssignBoundary Γ σ a
  postEq : boundary.post = σ₁
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Declaration execution leaves a certified stable post-state surface. -/
structure DeclBoundaryStability
    (Γ Δ : TypeEnv) (σ σ₁ : State) (d : CppDecl) : Type where
  boundary : Boundary.DeclBoundary Γ Δ σ d
  postEq : boundary.post = σ₁
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Expression-statement execution leaves a certified stable post-state surface. -/
structure ExprStmtBoundaryStability
    (Γ : TypeEnv) (σ σ₁ : State) (es : CppExprStmt) : Type where
  boundary : Boundary.ExprStmtBoundary Γ σ es
  postEq : boundary.post = σ₁
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Jump execution leaves a certified stable post-state surface. -/
structure JumpBoundaryStability
    (Γ : TypeEnv) (σ σ₁ : State) (j : CppJump) (r : CtrlResult) : Type where
  boundary : Boundary.JumpBoundary Γ σ j
  resultEq : boundary.result = r
  postEq : boundary.post = σ₁
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Return-payload stability, before it is wrapped as a jump. -/
structure ReturnBoundaryStability
    (Γ : TypeEnv) (σ : State) (r : CppReturn) : Type where
  boundary : Boundary.ReturnBoundary Γ σ r
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

end Stability
end Cpp3
