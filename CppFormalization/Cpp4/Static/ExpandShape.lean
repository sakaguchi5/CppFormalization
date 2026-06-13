import CppFormalization.Cpp4.Core.Expand
import CppFormalization.Cpp4.Static.ForShape
import CppFormalization.Cpp4.Static.SwitchShape

/-!
# CppFormalization.Cpp4.Static.ExpandShape

Static shape of expanded ControlPlan syntax and surface-to-plan expansion packages.

This file does not prove a full inversion theorem for every surface certificate.
It provides the ControlPlan-side static vocabulary and packages saying that a
surface fragment and its expansion are both statically shaped.
-/

namespace Cpp4

/-- Static shape of primitive ControlPlan atoms. -/
inductive StaticControlAtomShape : ControlAtom → Prop where
  | skip : StaticControlAtomShape .skip
  | exprStmt {s : CppExprStmt} : StaticExprStmtShape s → StaticControlAtomShape (.exprStmt s)
  | assign {a : CppAssign} : StaticAssignShape a → StaticControlAtomShape (.assign a)
  | decl {d : CppDecl} : StaticDeclShape d → StaticControlAtomShape (.decl d)
  | jump {j : CppJump} : StaticJumpShape j → StaticControlAtomShape (.jump j)

mutual

/-- Static shape of ControlPlan syntax. -/
inductive StaticPlanShape : ControlPlan → Prop where
  | atom {a : ControlAtom} : StaticControlAtomShape a → StaticPlanShape (.atom a)
  | seq {p q : ControlPlan} : StaticPlanShape p → StaticPlanShape q → StaticPlanShape (.seq p q)
  | branch {c : CppCond} {p q : ControlPlan} :
      StaticCondShape c → StaticPlanShape p → StaticPlanShape q →
      StaticPlanShape (.branch c p q)
  | scopeFrame {b : PlanBlock} : StaticPlanBlockShape b → StaticPlanShape (.scopeFrame b)
  | loopFrame {l : LoopPlan} : StaticLoopPlanShape l → StaticPlanShape (.loopFrame l)
  | switchFrame {c : CppSwitchCond} {arms : SwitchPlanArmList} :
      StaticSwitchCondShape c → StaticSwitchPlanArmListShape arms →
      StaticPlanShape (.switchFrame c arms)
  | switchSuffix {arms : SwitchPlanArmList} :
      StaticSwitchPlanArmListShape arms → StaticPlanShape (.switchSuffix arms)

/-- Static shape of PlanBlock syntax. -/
inductive StaticPlanBlockShape : PlanBlock → Prop where
  | nil : StaticPlanBlockShape .nil
  | cons {p : ControlPlan} {rest : PlanBlock} :
      StaticPlanShape p → StaticPlanBlockShape rest → StaticPlanBlockShape (.cons p rest)

/-- Static shape of LoopPlan syntax. -/
inductive StaticLoopPlanShape : LoopPlan → Prop where
  | preTest {c : CppCond} {body : ControlPlan} :
      StaticCondShape c → StaticPlanShape body → StaticLoopPlanShape (.preTest c body)
  | postTest {body : ControlPlan} {c : CppCond} :
      StaticPlanShape body → StaticCondShape c → StaticLoopPlanShape (.postTest body c)
  | forFrame {init : CppForInit} {cond : Option CppCond}
      {iter : CppForIter} {body : ControlPlan} :
      StaticForInitShape init → StaticFor.OptionalCondShape cond →
      StaticForIterShape iter → StaticPlanShape body →
      StaticLoopPlanShape (.forFrame init cond iter body)

/-- Static shape of one expanded switch arm. -/
inductive StaticSwitchPlanArmShape : SwitchPlanArm → Prop where
  | arm {label : SwitchLabel} {body : PlanBlock} :
      StaticSwitchLabelShape label → StaticPlanBlockShape body →
      StaticSwitchPlanArmShape (.arm label body)

/-- Static shape of expanded switch-arm lists. -/
inductive StaticSwitchPlanArmListShape : SwitchPlanArmList → Prop where
  | nil : StaticSwitchPlanArmListShape .nil
  | cons {arm : SwitchPlanArm} {rest : SwitchPlanArmList} :
      StaticSwitchPlanArmShape arm → StaticSwitchPlanArmListShape rest →
      StaticSwitchPlanArmListShape (.cons arm rest)

end

/-- A surface statement and its expanded plan are both statically shaped. -/
structure StmtExpandStaticShape (s : CppStmt) : Type where
  surfaceShape : StaticStmtShape s
  planShape : StaticPlanShape (expandStmt s)

/-- A surface block and its expanded plan block are both statically shaped. -/
structure BlockExpandStaticShape (b : StmtBlock) : Type where
  surfaceShape : StaticBlockShape b
  planShape : StaticPlanBlockShape (expandBlock b)

/-- A surface loop and its expanded plan are both statically shaped. -/
structure LoopExpandStaticShape (l : CppLoop) : Type where
  surfaceShape : StaticLoopShape l
  planShape : StaticPlanShape (expandLoop l)

/-- A surface switch arm and its expanded plan arm are both statically shaped. -/
structure SwitchArmExpandStaticShape (arm : SwitchArm) : Type where
  surfaceShape : StaticSwitchArmShape arm
  planShape : StaticSwitchPlanArmShape (expandSwitchArm arm)

/-- A surface switch-arm list and its expanded plan-arm list are both statically
shaped. -/
structure SwitchArmListExpandStaticShape (arms : SwitchArmList) : Type where
  surfaceShape : StaticSwitchArmListShape arms
  planShape : StaticSwitchPlanArmListShape (expandSwitchArms arms)

end Cpp4
