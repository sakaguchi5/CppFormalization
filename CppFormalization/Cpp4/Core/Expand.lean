import CppFormalization.Cpp4.Core.ControlPlan

/-!
# CppFormalization.Cpp4.Core.Expand

Expansion from C++-shaped surface Core syntax to the smaller structured-control
plan layer.

This is not Source-to-Core lowering.  Both sides are Core: `Syntax` is the
C++-facing structured surface, and `ControlPlan` is the atomized control layer
used by later semantics and proof assembly.
-/

namespace Cpp4

mutual

/-- Expand a surface Core statement into an atomic structured-control plan. -/
def expandStmt : CppStmt → ControlPlan
  | .skip => .atom .skip
  | .exprStmt e => .atom (.exprStmt e)
  | .assign a => .atom (.assign a)
  | .decl d => .atom (.decl d)
  | .seq s t => .seq (expandStmt s) (expandStmt t)
  | .ite c s t => .branch c (expandStmt s) (expandStmt t)
  | .loop l => expandLoop l
  | .switchStmt c arms => .switchFrame c (expandSwitchArms arms)
  | .block b => .scopeFrame (expandBlock b)
  | .jump j => .atom (.jump j)

/-- Expand a surface Core block. -/
def expandBlock : StmtBlock → PlanBlock
  | .nil => .nil
  | .cons s ss => .cons (expandStmt s) (expandBlock ss)

/-- Expand a structured loop. -/
def expandLoop : CppLoop → ControlPlan
  | .whileLoop c body => .loopFrame (.preTest c (expandStmt body))
  | .doWhileLoop body c => .loopFrame (.postTest (expandStmt body) c)
  | .forLoop init cond iter body =>
      .loopFrame (.forFrame init cond iter (expandStmt body))

/-- Expand switch arms from the surface custom list into the plan custom list. -/
def expandSwitchArms : SwitchArmList → SwitchPlanArmList
  | .nil => .nil
  | .cons a as => .cons (expandSwitchArm a) (expandSwitchArms as)

/-- Expand one switch arm. -/
def expandSwitchArm : SwitchArm → SwitchPlanArm
  | .arm l b => .arm l (expandBlock b)

end

namespace CppStmt

/-- Surface statement plan. -/
def controlPlan (s : CppStmt) : ControlPlan :=
  expandStmt s

end CppStmt

namespace StmtBlock

/-- Surface block plan. -/
def controlPlan (b : StmtBlock) : PlanBlock :=
  expandBlock b

end StmtBlock

namespace CppLoop

/-- Surface loop plan. -/
def controlPlan (l : CppLoop) : ControlPlan :=
  expandLoop l

end CppLoop

namespace SwitchArm

/-- Atomic plan arm for a surface switch arm. -/
def controlPlanArm (a : SwitchArm) : SwitchPlanArm :=
  expandSwitchArm a

end SwitchArm

namespace SwitchArmList

/-- Atomic plan arm list for a surface switch arm list. -/
def controlPlanArms (arms : SwitchArmList) : SwitchPlanArmList :=
  expandSwitchArms arms

end SwitchArmList

end Cpp4
