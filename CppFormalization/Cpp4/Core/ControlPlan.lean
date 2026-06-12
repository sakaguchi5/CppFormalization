import CppFormalization.Cpp4.Core.Syntax

/-!
# CppFormalization.Cpp4.Core.ControlPlan

The first, more atomic Core layer for structured control.

`Core.Syntax` keeps C++-shaped constructs such as `while`, `do while`, `for`,
and normalized `switch`.  This file gives the smaller structured-control atoms
that later semantics, demand transport, and soundness should primarily target.

This is intentionally not a low-level CFG/goto language.  The atoms are still
structured: sequence, branch, scope frame, loop frame, switch frame, and selected
fallthrough suffix.
-/

namespace Cpp4

/-- Primitive statement actions that do not themselves decompose control flow. -/
inductive ControlAtom where
  | skip
  | exprStmt : CppExprStmt → ControlAtom
  | assign : CppAssign → ControlAtom
  | decl : CppDecl → ControlAtom
  | jump : CppJump → ControlAtom
  deriving DecidableEq, Repr

mutual

/-- Atomic structured-control plan.

`scopeFrame` is deliberately not named `scoped`, because `scoped` is a Lean
keyword. -/
inductive ControlPlan where
  | atom : ControlAtom → ControlPlan
  | seq : ControlPlan → ControlPlan → ControlPlan
  | branch : CppCond → ControlPlan → ControlPlan → ControlPlan
  | scopeFrame : PlanBlock → ControlPlan
  | loopFrame : LoopPlan → ControlPlan
  /-- Normalized switch: evaluate the condition, choose an entry arm, then run
  the selected fallthrough suffix under switch break-capture. -/
  | switchFrame : CppSwitchCond → SwitchPlanArmList → ControlPlan
  /-- Already-selected switch suffix.  This is the atomic target for proving
  fallthrough transport separately from condition/case selection. -/
  | switchSuffix : SwitchPlanArmList → ControlPlan
  deriving DecidableEq, Repr

/-- Atomic block plan. -/
inductive PlanBlock where
  | nil
  | cons : ControlPlan → PlanBlock → PlanBlock
  deriving DecidableEq, Repr

/-- Loop plans make the continue target explicit enough for `for`.

`preTest` is while-like: condition before body, continue goes back to condition.
`postTest` is do-while-like: body runs first, normal/continue goes to condition.
`forFrame` is for-like: body normal/continue goes to iteration, then condition
or body reentry depending on whether the condition is present.
-/
inductive LoopPlan where
  | preTest : CppCond → ControlPlan → LoopPlan
  | postTest : ControlPlan → CppCond → LoopPlan
  | forFrame : CppForInit → Option CppCond → CppForIter → ControlPlan → LoopPlan
  deriving DecidableEq, Repr

/-- One switch arm in the atomic control-plan layer. -/
inductive SwitchPlanArm where
  | arm : SwitchLabel → PlanBlock → SwitchPlanArm
  deriving DecidableEq, Repr

/-- Switch arms in the atomic layer.

Do not use `List SwitchPlanArm` here: this type participates in the same mutual
recursion as `ControlPlan`, because each arm contains a `PlanBlock`, and each
`PlanBlock` contains `ControlPlan`s.  A custom list keeps the recursive family
inside one mutual inductive block and avoids nested-recursive positivity issues.
-/
inductive SwitchPlanArmList where
  | nil
  | cons : SwitchPlanArm → SwitchPlanArmList → SwitchPlanArmList
  deriving DecidableEq, Repr

end

namespace PlanBlock

def ofList : List ControlPlan → PlanBlock
  | [] => .nil
  | p :: ps => .cons p (ofList ps)

def toList : PlanBlock → List ControlPlan
  | .nil => []
  | .cons p ps => p :: toList ps

end PlanBlock

namespace ControlPlan

/-- A block plan as a sequential statement plan. -/
def ofBlock : PlanBlock → ControlPlan
  | .nil => .atom .skip
  | .cons p ps => .seq p (ofBlock ps)

end ControlPlan

namespace SwitchPlanArm

def label : SwitchPlanArm → SwitchLabel
  | .arm l _ => l

def body : SwitchPlanArm → PlanBlock
  | .arm _ b => b

end SwitchPlanArm

namespace SwitchPlanArmList

def ofList : List SwitchPlanArm → SwitchPlanArmList
  | [] => .nil
  | arm :: rest => .cons arm (ofList rest)

def toList : SwitchPlanArmList → List SwitchPlanArm
  | .nil => []
  | .cons arm rest => arm :: rest.toList

def length : SwitchPlanArmList → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

end SwitchPlanArmList

end Cpp4
