import CppFormalization.Cpp4.Static.SyntaxShape

/-!
# CppFormalization.Cpp4.Static.SwitchShape

Static surface facts specific to normalized Cpp4 switch syntax.
-/

namespace Cpp4

namespace SwitchLabel

/-- Extract an integer case value, if this label is a case label. -/
def caseValue? : SwitchLabel → Option Int
  | .caseInt n => some n
  | .defaultLabel => none

/-- Whether a label is `default`. -/
def IsDefault : SwitchLabel → Prop
  | .defaultLabel => True
  | .caseInt _ => False

end SwitchLabel

namespace SwitchArm

/-- Integer case value carried by an arm, if any. -/
def caseValue? (arm : SwitchArm) : Option Int :=
  arm.label.caseValue?

/-- Whether this arm has a default label. -/
def IsDefault (arm : SwitchArm) : Prop :=
  arm.label.IsDefault

end SwitchArm

namespace SwitchArmList

/-- Case values in fallthrough order, excluding `default`. -/
def caseValues : SwitchArmList → List Int
  | .nil => []
  | .cons arm rest =>
      match arm.caseValue? with
      | none => rest.caseValues
      | some n => n :: rest.caseValues

/-- Number of `default` labels. -/
def defaultCount : SwitchArmList → Nat
  | .nil => 0
  | .cons (.arm .defaultLabel _) rest => rest.defaultCount + 1
  | .cons (.arm (.caseInt _) _) rest => rest.defaultCount

/-- No duplicate integer case labels. -/
def NoDuplicateCases (arms : SwitchArmList) : Prop :=
  arms.caseValues.Nodup

/-- `default` appears at most once. -/
def DefaultAtMostOne (arms : SwitchArmList) : Prop :=
  arms.defaultCount ≤ 1

end SwitchArmList

/-- Stronger static shape for a switch-arm list: structural shape plus label
well-formedness constraints that are independent of typing. -/
structure SwitchArmListStaticShape (arms : SwitchArmList) : Type where
  structural : StaticSwitchArmListShape arms
  noDuplicateCases : arms.NoDuplicateCases
  defaultAtMostOne : arms.DefaultAtMostOne

/-- Static shape of a complete surface switch statement. -/
structure SwitchStmtStaticShape (cond : CppSwitchCond) (arms : SwitchArmList) : Type where
  condShape : StaticSwitchCondShape cond
  armsShape : SwitchArmListStaticShape arms

namespace SwitchStmtStaticShape

/-- Forget the switch-specific uniqueness facts and recover generic statement shape. -/
def toStaticStmtShape {cond : CppSwitchCond} {arms : SwitchArmList}
    (h : SwitchStmtStaticShape cond arms) :
    StaticStmtShape (.switchStmt cond arms) :=
  StaticStmtShape.switchStmt h.condShape h.armsShape.structural

end SwitchStmtStaticShape

end Cpp4
