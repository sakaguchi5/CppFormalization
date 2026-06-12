import CppFormalization.Cpp4.Core.Expand
import CppFormalization.Cpp4.Typing.Judgment.Surface.Program
import CppFormalization.Cpp4.Typing.Judgment.Surface.Loop
import CppFormalization.Cpp4.Typing.Judgment.Surface.Switch
import CppFormalization.Cpp4.Typing.Judgment.Plan.Loop
import CppFormalization.Cpp4.Typing.Judgment.Plan.Switch

/-!
# CppFormalization.Cpp4.Typing.Judgment.Expand

Expansion preservation for typing.

This layer builds `ControlPlan` typing certificates for the expanded plan of a
surface C++ Core fragment.  The constructors intentionally mirror the surface
syntax and target `expandStmt`, `expandBlock`, and `expandSwitchArms`.

Because the current surface typing certificates are records rather than
invertible inductive derivations, this file provides expansion-preserving
constructors instead of pretending that an arbitrary `SurfaceStmtTyping` record
can be destructed back into its original subderivations.
-/

namespace Cpp4

namespace TypingExpand

/-! ## Statement expansion -/

/-- Expanded typing for a surface `skip` statement. -/
def stmtSkip (Γ : TypeEnv) (κ : ControlContext) :
    PlanTyping Γ κ (expandStmt .skip) :=
  PlanTyping.atom (PlanAtomTyping.ofMicro
    (AtomTyping.skip : AtomTyping Γ κ .skip))

/-- Expanded typing for a surface expression statement. -/
def stmtExpr {Γ : TypeEnv} {κ : ControlContext} {s : CppExprStmt}
    (h : ExprStmtTyping Γ s) :
    PlanTyping Γ κ (expandStmt (.exprStmt s)) :=
  PlanTyping.atom (PlanAtomTyping.ofMicro
    (AtomTyping.exprStmt h : AtomTyping Γ κ (.exprStmt s)))

/-- Expanded typing for a surface assignment statement. -/
def stmtAssign {Γ : TypeEnv} {κ : ControlContext} {a : CppAssign}
    (h : AssignTyping Γ a) :
    PlanTyping Γ κ (expandStmt (.assign a)) :=
  PlanTyping.atom (PlanAtomTyping.ofMicro
    (AtomTyping.assign h : AtomTyping Γ κ (.assign a)))

/-- Expanded typing for a surface declaration statement. -/
def stmtDecl {Γ : TypeEnv} {κ : ControlContext} {d : CppDecl}
    (h : DeclTyping Γ d) :
    PlanTyping Γ κ (expandStmt (.decl d)) :=
  PlanTyping.atom (PlanAtomTyping.ofMicro
    (AtomTyping.decl h : AtomTyping Γ κ (.decl d)))

/-- Expanded typing for a surface sequence.  The tail is checked in the
post-environment produced by the expanded head. -/
def stmtSeq {Γ : TypeEnv} {κ : ControlContext} {head tail : CppStmt}
    (hHead : PlanTyping Γ κ (expandStmt head))
    (hTail : PlanTyping hHead.target κ (expandStmt tail)) :
    PlanTyping Γ κ (expandStmt (.seq head tail)) :=
  PlanTyping.seq hHead hTail

/-- Expanded typing for a surface conditional statement. -/
def stmtIte {Γ : TypeEnv} {κ : ControlContext} {c : CppCond}
    {thenStmt elseStmt : CppStmt}
    (hCond : CondTyping Γ c)
    (hThen : PlanTyping Γ κ (expandStmt thenStmt))
    (hElse : PlanTyping Γ κ (expandStmt elseStmt)) :
    PlanTyping Γ κ (expandStmt (.ite c thenStmt elseStmt)) :=
  PlanTyping.branch hCond hThen hElse

/-- Expanded typing for a surface block statement. -/
def stmtBlock {Γ : TypeEnv} {κ : ControlContext} {body : StmtBlock}
    (hBody : PlanBlockTyping Γ κ (expandBlock body)) :
    PlanTyping Γ κ (expandStmt (.block body)) :=
  PlanTyping.scopeFrame hBody

/-- Expanded typing for a surface jump statement. -/
def stmtJump {Γ : TypeEnv} {κ : ControlContext} {j : CppJump}
    (h : JumpTyping κ j) :
    PlanTyping Γ κ (expandStmt (.jump j)) :=
  PlanTyping.atom (PlanAtomTyping.ofMicro
    (AtomTyping.jump h : AtomTyping Γ κ (.jump j)))

/-! ## Block expansion -/

/-- Expanded typing for an empty surface block. -/
def blockNil (Γ : TypeEnv) (κ : ControlContext) :
    PlanBlockTyping Γ κ (expandBlock .nil) :=
  PlanBlockTyping.nil Γ κ

/-- Expanded typing for a nonempty surface block.  The tail is checked in the
post-environment produced by the expanded head statement. -/
def blockCons {Γ : TypeEnv} {κ : ControlContext}
    {head : CppStmt} {tail : StmtBlock}
    (hHead : PlanTyping Γ κ (expandStmt head))
    (hTail : PlanBlockTyping hHead.target κ (expandBlock tail)) :
    PlanBlockTyping Γ κ (expandBlock (.cons head tail)) :=
  PlanBlockTyping.cons hHead hTail

/-! ## Loop expansion -/

/-- Expanded typing for a surface `while` loop statement. -/
def stmtWhile {Γ : TypeEnv} {κ : ControlContext} {c : CppCond} {body : CppStmt}
    (hCond : CondTyping Γ c)
    (hBody : PlanTyping Γ (ControlContext.loopBody κ) (expandStmt body)) :
    PlanTyping Γ κ (expandStmt (.loop (.whileLoop c body))) :=
  PlanTyping.loopFrame (LoopPlanTyping.preTest hCond hBody)

/-- Expanded typing for a surface `do while` loop statement. -/
def stmtDoWhile {Γ : TypeEnv} {κ : ControlContext} {body : CppStmt} {c : CppCond}
    (hBody : PlanTyping Γ (ControlContext.loopBody κ) (expandStmt body))
    (hCond : CondTyping Γ c) :
    PlanTyping Γ κ (expandStmt (.loop (.doWhileLoop body c))) :=
  PlanTyping.loopFrame (LoopPlanTyping.postTest hBody hCond)

/-- Expanded typing for a surface `for` loop statement.  The initializer may extend
only the loop-local environment used by the condition, body, and iteration step. -/
def stmtFor {Γ : TypeEnv} {κ : ControlContext}
    {init : CppForInit} {cond : Option CppCond} {iter : CppForIter} {body : CppStmt}
    (hInit : ForInitTyping Γ init)
    (hCond : OptionalCondTyping hInit.target cond)
    (hIter : ForIterTyping hInit.target iter)
    (hBody : PlanTyping hInit.target (ControlContext.loopBody κ) (expandStmt body)) :
    PlanTyping Γ κ (expandStmt (.loop (.forLoop init cond iter body))) :=
  PlanTyping.loopFrame (LoopPlanTyping.forFrame hInit hCond hIter hBody)

/-! ## Switch expansion -/

/-- Convert a surface switch-arm header certificate to the corresponding expanded
ControlPlan arm header certificate. -/
def switchPlanArmHeaderOfSurface {label : SwitchLabel} {body : StmtBlock}
    (h : SwitchArmHeaderTyping (.arm label body)) :
    SwitchPlanArmHeaderTyping (.arm label (expandBlock body)) where
  labelTyping := h.labelTyping

/-- Expanded typing for a single surface switch arm. -/
def switchArm {Γ : TypeEnv} {κ : ControlContext}
    {label : SwitchLabel} {body : StmtBlock}
    (hHeader : SwitchArmHeaderTyping (.arm label body))
    (hBody : PlanBlockTyping Γ κ (expandBlock body)) :
    SwitchPlanArmTyping Γ κ (expandSwitchArm (.arm label body)) :=
  SwitchPlanArmTyping.arm (switchPlanArmHeaderOfSurface hHeader) hBody

/-- Expanded typing for an empty surface switch-arm list. -/
def switchArmListNil (Γ : TypeEnv) (κ : ControlContext) :
    SwitchPlanArmListTyping Γ κ (expandSwitchArms .nil) :=
  SwitchPlanArmListTyping.nil Γ κ

/-- Expanded typing for a nonempty surface switch-arm list.  The rest of the
fallthrough suffix is checked in the post-environment produced by the head arm. -/
def switchArmListCons {Γ : TypeEnv} {κ : ControlContext}
    {arm : SwitchArm} {rest : SwitchArmList}
    (hArm : SwitchPlanArmTyping Γ κ (expandSwitchArm arm))
    (hRest : SwitchPlanArmListTyping hArm.target κ (expandSwitchArms rest)) :
    SwitchPlanArmListTyping Γ κ (expandSwitchArms (.cons arm rest)) :=
  SwitchPlanArmListTyping.cons hArm hRest

/-- Expanded typing for a surface switch statement. -/
def stmtSwitch {Γ : TypeEnv} {κ : ControlContext}
    {cond : CppSwitchCond} {arms : SwitchArmList}
    (hCond : SwitchCondTyping Γ cond)
    (hArms : SwitchPlanArmListTyping Γ (switchArmControlContext κ)
      (expandSwitchArms arms)) :
    PlanTyping Γ κ (expandStmt (.switchStmt cond arms)) :=
  PlanTyping.switchFrame hCond hArms

/-! ## Function bodies -/

/-- Expanded plan-block typing for a function body. -/
structure FunctionBodyExpandTyping (sig : FunctionSig) (body : StmtBlock) : Type where
  planBodyTyping : PlanBlockTyping sig.bodyEnv (ControlContext.enterFunction sig.ret)
    (expandBlock body)
  formation : Prop
  evidence : formation

namespace FunctionBodyExpandTyping

/-- Build a function-body expansion certificate from an expanded block typing. -/
def ofPlanBlock {sig : FunctionSig} {body : StmtBlock}
    (hBody : PlanBlockTyping sig.bodyEnv (ControlContext.enterFunction sig.ret)
      (expandBlock body)) :
    FunctionBodyExpandTyping sig body where
  planBodyTyping := hBody
  formation := hBody.formation
  evidence := hBody.evidence

end FunctionBodyExpandTyping

end TypingExpand

end Cpp4
