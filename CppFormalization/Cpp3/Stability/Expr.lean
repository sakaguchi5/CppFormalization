import CppFormalization.Cpp3.Stability.Core

/-!
# CppFormalization.Cpp3.Stability.Expr

Stability packages for expression and condition boundaries.

These records do not re-evaluate expressions.  They name the fact that the
runtime boundary needed for an expression/condition remains available when a
later layer asks for it.
-/

namespace Cpp3
namespace Stability

/-- Stability package for a place boundary in a concrete state. -/
structure PlaceBoundaryStability
    (Γ : TypeEnv) (σ : State) (p : PlaceExpr) : Type where
  before : Boundary.PlaceBoundary Γ σ p
  after : Boundary.PlaceBoundary Γ σ p
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Stability package for a value-expression boundary in a concrete state. -/
structure ValBoundaryStability
    (Γ : TypeEnv) (σ : State) (e : ValExpr) : Type where
  before : Boundary.ValBoundary Γ σ e
  after : Boundary.ValBoundary Γ σ e
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Stability package for a condition boundary and its post-condition state. -/
structure CondBoundaryStability
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) : Type where
  before : Boundary.CondBoundary Γ Γc σ cond
  post : State
  postEq : before.post = post
  after : Boundary.CondBoundary Γ Γc σ cond
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

namespace CondBoundaryStability

/-- The post-state exposed by the stable condition boundary. -/
def postState
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond}
    (h : CondBoundaryStability Γ Γc σ cond) : State :=
  h.post

end CondBoundaryStability

end Stability
end Cpp3
