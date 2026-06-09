import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Divergent

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.OneIteration

One-iteration vocabulary for the while loop engine.

This file isolates the C++ operational cases of a single while iteration.  It is
not yet the full finite/divergent classification theorem.  It only names the
local outcomes that later trace and dichotomy layers consume:

* false guard exits the loop;
* true guard plus `break` exits the loop normally;
* true guard plus `return` propagates the return;
* true guard plus body divergence makes the whole while diverge;
* true guard plus body `normal`/`continue` re-enters the same while statement.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- A normal/continue body result that re-enters the same while statement. -/
inductive LoopReentryStep
    (σ : State) (cond : CppCond) (body : CppStmt) : State → Type where
  | bodyNormal
      {σc σb : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyStep : Semantics.BigStepStmt σc body .normal σb) :
      LoopReentryStep σ cond body σb
  | bodyContinue
      {σc σb : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyStep : Semantics.BigStepStmt σc body .continueResult σb) :
      LoopReentryStep σ cond body σb

namespace LoopReentryStep

/-- Extend a classified tail loop through one reentry step. -/
def extendBigStep
    {σ σb σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (h : LoopReentryStep σ cond body σb)
    (tail : Semantics.BigStepStmt σb (.whileStmt cond body) r σout) :
    Semantics.BigStepStmt σ (.whileStmt cond body) r σout :=
  match h with
  | .bodyNormal condTrue bodyStep =>
      Semantics.BigStepStmt.whileBodyNormal condTrue bodyStep tail
  | .bodyContinue condTrue bodyStep =>
      Semantics.BigStepStmt.whileBodyContinue condTrue bodyStep tail

/-- Project the post-state reached by the reentry step. -/
def postState
    {σ σb : State} {cond : CppCond} {body : CppStmt}
    (_h : LoopReentryStep σ cond body σb) : State :=
  σb

end LoopReentryStep

/-- The C++ outcomes of one while iteration.

This deliberately separates reentry from finite exits and divergence.  A later
trace layer decides whether repeated reentries eventually terminate or continue
forever. -/
inductive OneIterationOutcome
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | falseExit
      {σc : State}
      (condFalse : Semantics.BigStepCond σ cond false σc) :
      OneIterationOutcome σ cond body
  | breakExit
      {σc σb : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyBreak : Semantics.BigStepStmt σc body .breakResult σb) :
      OneIterationOutcome σ cond body
  | returnExit
      {σc σb : State} {ov : Option Value}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyReturn : Semantics.BigStepStmt σc body (.returnResult ov) σb) :
      OneIterationOutcome σ cond body
  | bodyDiverges
      {σc : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyDiv : Semantics.StmtDiv σc body) :
      OneIterationOutcome σ cond body
  | reenters
      {σb : State}
      (step : LoopReentryStep σ cond body σb) :
      OneIterationOutcome σ cond body

end LoopEngine
end Derive
end Soundness
end Cpp3
