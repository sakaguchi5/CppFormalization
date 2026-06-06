import CppFormalization.Cpp3.Core.Syntax

/-!
Syntactic fragment markers for the currently supported big-step core.

These are syntax-only predicates.  The name mentions big-step because the
fragment is the one consumed by the operational semantics, but no semantic
judgment is used here.
-/

namespace Cpp3

/-- Condition fragment for the current expression-only condition core. -/
def InBigStepCondFragment : CppCond → Prop
  | .expr _ => True

/-- Initializer fragment for the current expression-only declaration core. -/
def InBigStepInitFragment : CppInit → Prop
  | .noInit => True
  | .value _ => True

/-- Declaration fragment for the current object/reference declaration core. -/
def InBigStepDeclFragment : CppDecl → Prop
  | .object _ _ init => InBigStepInitFragment init
  | .ref _ _ _ => True

/-- Return-payload fragment for the current expression-only return core. -/
def InBigStepReturnFragment : CppReturn → Prop
  | .void => True
  | .value _ => True

/-- Jump fragment for the current break/continue/return core. -/
def InBigStepJumpFragment : CppJump → Prop
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt r => InBigStepReturnFragment r

/-- Assignment fragment for the current simple-assignment core. -/
def InBigStepAssignFragment : CppAssign → Prop
  | .simple _ _ => True

/-- Expression-statement fragment for the current discarded-expression core. -/
def InBigStepExprStmtFragment : CppExprStmt → Prop
  | .discard _ => True

mutual

def InBigStepFragment : CppStmt → Prop
  | .skip => True
  | .exprStmt es => InBigStepExprStmtFragment es
  | .assign a => InBigStepAssignFragment a
  | .decl d => InBigStepDeclFragment d
  | .seq s t => InBigStepFragment s ∧ InBigStepFragment t
  | .ite c s t => InBigStepCondFragment c ∧ InBigStepFragment s ∧ InBigStepFragment t
  | .whileStmt c body => InBigStepCondFragment c ∧ InBigStepFragment body
  | .block ss => InBigStepBlockFragment ss
  | .jump j => InBigStepJumpFragment j

def InBigStepBlockFragment : StmtBlock → Prop
  | .nil => True
  | .cons s ss => InBigStepFragment s ∧ InBigStepBlockFragment ss

end

def CoreBigStepFragment (st : CppStmt) : Prop :=
  InBigStepFragment st

end Cpp3
