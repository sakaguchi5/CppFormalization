import CppFormalization.Cpp4.Core.ControlPlan
import CppFormalization.Cpp4.Resource.Demand.Call

/-!
# CppFormalization.Cpp4.Resource.Demand.Atom

Demand surfaces for `Core.ControlPlan` atoms.

This layer deliberately does not try to type-check expressions or places.  It
packages already-computed expression/place/call demand fragments so Typing can
later provide precise demands without changing the ControlPlan transport layer.
-/

namespace Cpp4

/-- Resource demand required to enter a primitive control atom. -/
structure AtomDemand where
  demands : DemandSet

/-- Resource demand required to enter a ControlPlan. -/
structure PlanDemand where
  demands : DemandSet

/-- Resource demand required to enter a plan block. -/
structure PlanBlockDemand where
  demands : DemandSet

/-- Resource demand required to enter a loop plan. -/
structure LoopDemand where
  demands : DemandSet

/-- Resource demand required to enter a switch frame or selected switch suffix. -/
structure SwitchDemand where
  demands : DemandSet

namespace AtomDemand

/-- Empty atom demand.  Used for structural atoms whose precise resource demand
will be supplied by later Typing layers. -/
def empty : AtomDemand where
  demands := []

/-- Build an atom demand from a raw demand set. -/
def ofDemandSet (D : DemandSet) : AtomDemand where
  demands := D

/-- `skip` requires no runtime resource. -/
def skip : AtomDemand :=
  empty

/-- Expression statements inherit the demand of the discarded expression. -/
def exprStmt (e : ExprDemand) : AtomDemand where
  demands := e.demands

/-- Assignment combines the demand of the destination place and the source
expression.  The precise read/write flavor of the destination is chosen by the
future typing/micro layer that constructs the `PlaceDemand`. -/
def assign (dst : PlaceDemand) (src : ExprDemand) : AtomDemand where
  demands := dst.demands ++ src.demands

/-- Object declaration without initializer needs only its lower declaration
resource surface, supplied later by typing/static layers. -/
def declRaw (D : DemandSet) : AtomDemand :=
  ofDemandSet D

/-- A declaration with an initializer also requires the initializer demand. -/
def declWithInit (base : DemandSet) (init : ExprDemand) : AtomDemand where
  demands := base ++ init.demands

/-- A reference declaration inherits the referenced-place demand in addition to
any declaration-local resource obligations supplied by typing/static layers. -/
def declRef (base : DemandSet) (target : PlaceDemand) : AtomDemand where
  demands := base ++ target.demands

/-- A jump atom requires the corresponding control permission demand. -/
def jump : CppJump → AtomDemand
  | .breakStmt => { demands := [.breakAllowed] }
  | .continueStmt => { demands := [.continueAllowed] }
  | .returnStmt .void => { demands := [] }
  | .returnStmt (.value _) => { demands := [] }

/-- A return atom with a known return type.  This is the typed form that later
Typing should use instead of the untyped `jump` fallback above. -/
def returnAllowed (τ : CppType) : AtomDemand where
  demands := [.returnAllowed τ]

/-- Conservative structural atom demand from syntax alone.  Precise demands for
expressions, assignments, declarations, and typed returns are intentionally
provided by the typed constructors above. -/
def structural : ControlAtom → AtomDemand
  | .skip => skip
  | .exprStmt _ => empty
  | .assign _ => empty
  | .decl _ => empty
  | .jump j => jump j

end AtomDemand

end Cpp4
