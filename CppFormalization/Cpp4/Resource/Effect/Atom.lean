import CppFormalization.Cpp4.Resource.Effect.Stmt
import CppFormalization.Cpp4.Resource.Demand.Atom

/-!
# CppFormalization.Cpp4.Resource.Effect.Atom

Effect surfaces for ControlPlan atoms.
-/

namespace Cpp4

/-- Resource effect produced by a primitive control atom. -/
structure AtomEffect where
  effect : ResourceEffect

/-- Resource effect produced by a ControlPlan. -/
structure PlanEffect where
  effect : ResourceEffect

/-- Resource effect produced by a plan block. -/
structure PlanBlockEffect where
  effect : ResourceEffect

/-- Resource effect produced by a loop plan. -/
structure LoopEffect where
  effect : ResourceEffect

/-- Resource effect produced by a switch frame or selected switch suffix. -/
structure SwitchEffect where
  effect : ResourceEffect

namespace AtomEffect

/-- Empty atom effect. -/
def empty : AtomEffect where
  effect := []

/-- Build an atom effect from a raw trace. -/
def ofEffect (eff : ResourceEffect) : AtomEffect where
  effect := eff

/-- `skip` has no resource effect. -/
def skip : AtomEffect :=
  empty

/-- Expression statements carry the effect of expression evaluation, supplied by
future expression semantics. -/
def exprStmt (eff : ResourceEffect) : AtomEffect :=
  ofEffect eff

/-- Assignment atom effect, supplied by assignment semantics. -/
def assign (eff : ResourceEffect) : AtomEffect :=
  ofEffect eff

/-- Declaration atom effect, supplied by declaration semantics. -/
def decl (eff : ResourceEffect) : AtomEffect :=
  ofEffect eff

/-- Control-transfer atom effect. -/
def control (r : CtrlResult) : AtomEffect where
  effect := [.control r]

/-- Conservative structural atom effect from syntax alone.  Precise expression,
assignment, declaration, and return-value effects are supplied later by typed
semantics. -/
def structural : ControlAtom → AtomEffect
  | .skip => skip
  | .exprStmt _ => empty
  | .assign _ => empty
  | .decl _ => empty
  | .jump .breakStmt => control .breakResult
  | .jump .continueStmt => control .continueResult
  | .jump (.returnStmt .void) => control .returnVoid
  | .jump (.returnStmt (.value _)) => empty

end AtomEffect

end Cpp4
