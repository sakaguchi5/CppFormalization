import CppFormalization.Cpp3.Static.Scope

/-!
# CppFormalization.Cpp3.Static.ControlProfile

Syntax-level control profile for Cpp3 statements and block bodies.

This profile is intentionally weaker than `Typing.Judgment`: it records which
control channels are visible from the syntax/control shape, not whether the
program is fully typed, ready, stable, or contract-satisfying.
-/

namespace Cpp3
namespace Static

/-- Abrupt control channels that short-circuit sequencing and block-cons. -/
def StaticAbruptControl : ControlKind → Prop
  | .normalK => False
  | .breakK => True
  | .continueK => True
  | .returnK => True

mutual

/-- Syntax-level statement control profile. -/
inductive StaticStmtControl : CppStmt → ControlKind → Prop where
  | skip :
      StaticStmtControl .skip .normalK

  | exprStmt
      {e : CppExprStmt} :
      StaticExprStmtFormed e →
      StaticStmtControl (.exprStmt e) .normalK

  | assign
      {a : CppAssign} :
      StaticAssignFormed a →
      StaticStmtControl (.assign a) .normalK

  | decl
      {d : CppDecl} :
      StaticDeclFormed d →
      StaticStmtControl (.decl d) .normalK

  | jumpBreak :
      StaticStmtControl (.jump .breakStmt) .breakK

  | jumpContinue :
      StaticStmtControl (.jump .continueStmt) .continueK

  | jumpReturnVoid :
      StaticStmtControl (.jump (.returnStmt .void)) .returnK

  | jumpReturnValue
      {e : ValExpr} :
      StaticValFormed e →
      StaticStmtControl (.jump (.returnStmt (.value e))) .returnK

  | seqNormal
      {s t : CppStmt} {k : ControlKind} :
      StaticStmtControl s .normalK →
      StaticStmtControl t k →
      StaticStmtControl (.seq s t) k

  | seqAbrupt
      {s t : CppStmt} {k : ControlKind} :
      StaticAbruptControl k →
      StaticStmtControl s k →
      StaticStmtFormed t →
      StaticStmtControl (.seq s t) k

  | iteThen
      {cond : CppCond} {s t : CppStmt} {k : ControlKind} :
      StaticCondFormed cond →
      StaticStmtControl s k →
      StaticStmtFormed t →
      StaticStmtControl (.ite cond s t) k

  | iteElse
      {cond : CppCond} {s t : CppStmt} {k : ControlKind} :
      StaticCondFormed cond →
      StaticStmtFormed s →
      StaticStmtControl t k →
      StaticStmtControl (.ite cond s t) k

  | whileNormal
      {cond : CppCond} {body : CppStmt} :
      StaticCondFormed cond →
      StaticStmtFormed body →
      StaticStmtControl (.whileStmt cond body) .normalK

  | whileReturn
      {cond : CppCond} {body : CppStmt} :
      StaticCondFormed cond →
      StaticStmtControl body .returnK →
      StaticStmtControl (.whileStmt cond body) .returnK

  | block
      {ss : StmtBlock} {k : ControlKind} :
      StaticBlockControl ss k →
      StaticStmtControl (.block ss) k

/-- Syntax-level block-body control profile. -/
inductive StaticBlockControl : StmtBlock → ControlKind → Prop where
  | nil :
      StaticBlockControl .nil .normalK

  | consNormal
      {head : CppStmt} {tail : StmtBlock} {k : ControlKind} :
      StaticStmtControl head .normalK →
      StaticBlockControl tail k →
      StaticBlockControl (.cons head tail) k

  | consAbrupt
      {head : CppStmt} {tail : StmtBlock} {k : ControlKind} :
      StaticAbruptControl k →
      StaticStmtControl head k →
      StaticBlockFormed tail →
      StaticBlockControl (.cons head tail) k

end

/-- A statement control profile package. -/
structure StmtControlProfile (st : CppStmt) : Type where
  formed : StaticStmtFormed st
  canControl : ControlKind → Prop
  sound : ∀ {k : ControlKind}, canControl k → StaticStmtControl st k

/-- A block control profile package. -/
structure BlockControlProfile (ss : StmtBlock) : Type where
  formed : StaticBlockFormed ss
  canControl : ControlKind → Prop
  sound : ∀ {k : ControlKind}, canControl k → StaticBlockControl ss k

/-- The canonical statement profile uses `StaticStmtControl` itself. -/
def StmtControlProfile.canonical
    {st : CppStmt} (h : StaticStmtFormed st) : StmtControlProfile st where
  formed := h
  canControl := StaticStmtControl st
  sound := fun hcontrol => hcontrol

/-- The canonical block profile uses `StaticBlockControl` itself. -/
def BlockControlProfile.canonical
    {ss : StmtBlock} (h : StaticBlockFormed ss) : BlockControlProfile ss where
  formed := h
  canControl := StaticBlockControl ss
  sound := fun hcontrol => hcontrol

end Static
end Cpp3
