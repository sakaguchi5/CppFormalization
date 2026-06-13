import CppFormalization.Cpp4.Resource.Demand.All

/-!
# CppFormalization.Cpp4.Boundary.Core

Runtime boundary vocabulary derived from resource-demand satisfaction.

This layer is intentionally thin: it does not introduce new C++ semantics.  It
only gives names to the fact that a runtime state satisfies the demand set
computed by Typing/Resource layers.
-/

namespace Cpp4

/-- Generic runtime boundary for a raw demand set. -/
structure DemandBoundary (χ : DemandContext) (σ : State) (D : DemandSet) : Type where
  satisfied : DemandSetSatisfied χ σ D

namespace DemandBoundary

/-- Build a demand boundary from an already-known satisfaction proof. -/
def ofSatisfied {χ : DemandContext} {σ : State} {D : DemandSet}
    (h : DemandSetSatisfied χ σ D) : DemandBoundary χ σ D where
  satisfied := h

/-- Empty demand boundary. -/
def nil (χ : DemandContext) (σ : State) : DemandBoundary χ σ [] where
  satisfied := DemandSetSatisfied.nil χ σ

/-- Split a boundary for an appended demand set. -/
def leftOfAppend {χ : DemandContext} {σ : State} {D₁ D₂ : DemandSet}
    (h : DemandBoundary χ σ (D₁ ++ D₂)) : DemandBoundary χ σ D₁ where
  satisfied := DemandSetSatisfied.left_of_append h.satisfied

/-- Split a boundary for the right side of an appended demand set. -/
def rightOfAppend {χ : DemandContext} {σ : State} {D₁ D₂ : DemandSet}
    (h : DemandBoundary χ σ (D₁ ++ D₂)) : DemandBoundary χ σ D₂ where
  satisfied := DemandSetSatisfied.right_of_append h.satisfied

/-- Combine two boundaries for demand fragments at the same state. -/
def append {χ : DemandContext} {σ : State} {D₁ D₂ : DemandSet}
    (h₁ : DemandBoundary χ σ D₁) (h₂ : DemandBoundary χ σ D₂) :
    DemandBoundary χ σ (D₁ ++ D₂) where
  satisfied := DemandSetSatisfied.append h₁.satisfied h₂.satisfied

end DemandBoundary

namespace DemandContext

/-- Demand context induced by a static control context and a callable environment. -/
def ofControlAndFunctions (κ : ControlContext) (Φ : FunctionEnv) : DemandContext where
  control := κ
  functions := Φ

/-- A demand context uses the same control channel as a typing context. -/
def MatchesControl (χ : DemandContext) (κ : ControlContext) : Prop :=
  χ.control = κ

end DemandContext

end Cpp4
