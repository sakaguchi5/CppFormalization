import CppFormalization.Cpp3.Core.Syntax

/-!
Syntactic fragment markers for the currently supported big-step core.

These are syntax-only predicates.  The name mentions big-step because the
fragment is the one consumed by the operational semantics, but no semantic
judgment is used here.
-/

namespace Cpp3

mutual

def InBigStepFragment : CppStmt → Prop
  | .skip => True
  | .exprStmt _ => True
  | .assign _ _ => True
  | .declareObj _ _ _ => True
  | .declareRef _ _ _ => True
  | .seq s t => InBigStepFragment s ∧ InBigStepFragment t
  | .ite _ s t => InBigStepFragment s ∧ InBigStepFragment t
  | .whileStmt _ body => InBigStepFragment body
  | .block ss => InBigStepBlockFragment ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt _ => True

def InBigStepBlockFragment : StmtBlock → Prop
  | .nil => True
  | .cons s ss => InBigStepFragment s ∧ InBigStepBlockFragment ss

end

def CoreBigStepFragment (st : CppStmt) : Prop :=
  InBigStepFragment st

end Cpp3
