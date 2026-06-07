import CppFormalization.Cpp3.Boundary.Core
import CppFormalization.Cpp3.Semantics.Kernel.Value

/-!
# CppFormalization.Cpp3.Boundary.Expr

Runtime boundaries for places, values, and conditions.

These packages connect static/effect/safety surfaces to concrete semantic
entry/evaluation facts in a state.  They do not say that a later boundary is
preserved after execution.
-/

namespace Cpp3
namespace Boundary

/-- Runtime boundary for entering/evaluating a place expression. -/
structure PlaceBoundary (Γ : TypeEnv) (σ : State) (p : PlaceExpr) : Type where
  static : Static.StaticPlaceBoundaryInfo Γ p
  effect : Effects.PlaceEffect Γ p
  ty : CppType
  addr : Nat
  eval : Semantics.BigStepPlace σ p ty addr
  live : RuntimeLiveCell σ addr
  typed : RuntimeTypedCell σ addr ty
  safety : Prop
  safetyEvidence : Contracts.Requires safety

namespace PlaceBoundary

/-- The address selected by a place boundary. -/
def address {Γ : TypeEnv} {σ : State} {p : PlaceExpr}
    (h : PlaceBoundary Γ σ p) : Nat :=
  h.addr

/-- The type selected by a place boundary. -/
def placeType {Γ : TypeEnv} {σ : State} {p : PlaceExpr}
    (h : PlaceBoundary Γ σ p) : CppType :=
  h.ty

end PlaceBoundary

/-- Runtime boundary for evaluating a value expression. -/
structure ValBoundary (Γ : TypeEnv) (σ : State) (e : ValExpr) : Type where
  static : Static.StaticValBoundaryInfo Γ e
  effect : Effects.ValEffect Γ e
  safety : SafetyFragment.ValSafetyFragment Γ e
  ty : CppType
  value : Value
  eval : Semantics.BigStepValue σ e ty value
  compat : ValueCompat value ty

namespace ValBoundary

/-- The value produced by a value boundary. -/
def result {Γ : TypeEnv} {σ : State} {e : ValExpr}
    (h : ValBoundary Γ σ e) : Value :=
  h.value

/-- The result type of a value boundary. -/
def resultType {Γ : TypeEnv} {σ : State} {e : ValExpr}
    (h : ValBoundary Γ σ e) : CppType :=
  h.ty

end ValBoundary

/-- Runtime boundary for evaluating a condition. -/
structure CondBoundary
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) : Type where
  static : Static.StaticCondBoundaryInfo Γ Γc cond
  effect : Effects.CondEffect Γ Γc cond
  safety : SafetyFragment.CondSafetyFragment Γ Γc cond
  value : Bool
  post : State
  eval : Semantics.BigStepCond σ cond value post

namespace CondBoundary

/-- The boolean selected by a condition boundary. -/
def truth
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond}
    (h : CondBoundary Γ Γc σ cond) : Bool :=
  h.value

/-- The state after condition evaluation. -/
def postState
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond}
    (h : CondBoundary Γ Γc σ cond) : State :=
  h.post

end CondBoundary

end Boundary
end Cpp3
