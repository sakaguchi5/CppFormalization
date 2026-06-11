import CppFormalization.Cpp3.Semantics.Kernel.ClassificationLemmas

/-!
# CppFormalization.Cpp3.Semantics.Kernel.WhileTrace

Semantic trace vocabulary for while-loop finite and divergent behavior.

These traces are purely semantic.  They explain how a while statement either
produces a finite big-step result or diverges; they do not mention Soundness2,
boundaries, typing, safety, stability, or contracts.
-/

namespace Cpp3
namespace Semantics

/-- One reentry step of a while loop, through body normal or continue. -/
inductive LoopReentryStep (σ : State) (cond : CppCond) (body : CppStmt) : State → Type where
  | bodyNormal
      {σc σb : State}
      (condTrue : BigStepCond σ cond true σc)
      (bodyStep : BigStepStmt σc body .normal σb) :
      LoopReentryStep σ cond body σb
  | bodyContinue
      {σc σb : State}
      (condTrue : BigStepCond σ cond true σc)
      (bodyStep : BigStepStmt σc body .continueResult σb) :
      LoopReentryStep σ cond body σb

/-- Finite loop trace explanation.  This is an explanatory semantic trace, not a
hidden proof that all loops terminate. -/
inductive FiniteLoopTrace (cond : CppCond) (body : CppStmt) :
    State → CtrlResult → State → Type where
  | falseExit
      {σ σc : State}
      (condFalse : BigStepCond σ cond false σc) :
      FiniteLoopTrace cond body σ .normal σc

  | breakExit
      {σ σc σb : State}
      (condTrue : BigStepCond σ cond true σc)
      (bodyBreak : BigStepStmt σc body .breakResult σb) :
      FiniteLoopTrace cond body σ .normal σb

  | returnExit
      {σ σc σb : State} {ov : Option Value}
      (condTrue : BigStepCond σ cond true σc)
      (bodyReturn : BigStepStmt σc body (.returnResult ov) σb) :
      FiniteLoopTrace cond body σ (.returnResult ov) σb

  | reenter
      {σ σb σout : State} {r : CtrlResult}
      (step : LoopReentryStep σ cond body σb)
      (tail : FiniteLoopTrace cond body σb r σout) :
      FiniteLoopTrace cond body σ r σout

namespace FiniteLoopTrace

/-- A finite loop trace is exactly a finite big-step execution of the while
statement. -/
def bigStep
    {cond : CppCond} {body : CppStmt} {σ σout : State} {r : CtrlResult}
    (trace : FiniteLoopTrace cond body σ r σout) :
    BigStepStmt σ (.whileStmt cond body) r σout := by
  induction trace with
  | falseExit condFalse =>
      exact BigStepStmt.whileFalse condFalse
  | breakExit condTrue bodyBreak =>
      exact BigStepStmt.whileBodyBreak condTrue bodyBreak
  | returnExit condTrue bodyReturn =>
      exact BigStepStmt.whileBodyReturn condTrue bodyReturn
  | reenter step tail ih =>
      cases step with
      | bodyNormal condTrue bodyStep =>
          exact BigStepStmt.whileBodyNormal condTrue bodyStep ih
      | bodyContinue condTrue bodyStep =>
          exact BigStepStmt.whileBodyContinue condTrue bodyStep ih

/-- A finite loop trace classifies the while statement by termination. -/
def classification
    {cond : CppCond} {body : CppStmt} {σ σout : State} {r : CtrlResult}
    (trace : FiniteLoopTrace cond body σ r σout) :
    StmtClassified σ (.whileStmt cond body) :=
  stmtClassified_of_terminates ⟨r, σout, trace.bigStep⟩

end FiniteLoopTrace

/-- Divergent loop explanation. -/
inductive DivergentLoopTrace (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | bodyDiverges
      {σc : State}
      (condTrue : BigStepCond σ cond true σc)
      (bodyDiv : StmtDiv σc body) :
      DivergentLoopTrace σ cond body
  | forever
      (prefixes : ∀ n : Nat, ∃ σn : State,
        WhilePrefix n σ cond body σn) :
      DivergentLoopTrace σ cond body

namespace DivergentLoopTrace

/-- A divergent loop trace is exactly a statement-divergence proof for the while
statement. -/
def stmtDiv
    {σ : State} {cond : CppCond} {body : CppStmt}
    (trace : DivergentLoopTrace σ cond body) :
    StmtDiv σ (.whileStmt cond body) := by
  cases trace with
  | bodyDiverges condTrue bodyDiv =>
      exact StmtDiv.whileBody condTrue bodyDiv
  | forever prefixes =>
      exact StmtDiv.whileForever prefixes

/-- A divergent loop trace classifies the while statement by divergence. -/
def classification
    {σ : State} {cond : CppCond} {body : CppStmt}
    (trace : DivergentLoopTrace σ cond body) :
    StmtClassified σ (.whileStmt cond body) :=
  stmtClassified_of_div trace.stmtDiv

end DivergentLoopTrace

/-- Behavior explanation for one concrete while entry. -/
inductive LoopBehaviorSource
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | finite
      {σout : State} {r : CtrlResult}
      (trace : FiniteLoopTrace cond body σ r σout) :
      LoopBehaviorSource σ cond body
  | divergent
      (trace : DivergentLoopTrace σ cond body) :
      LoopBehaviorSource σ cond body

namespace LoopBehaviorSource

/-- Build a behavior source for body divergence. -/
def bodyDiverges
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condTrue : BigStepCond σ cond true σc)
    (bodyDiv : StmtDiv σc body) :
    LoopBehaviorSource σ cond body :=
  .divergent (.bodyDiverges condTrue bodyDiv)

/-- Build a behavior source for productive forever reentry. -/
def forever
    {σ : State} {cond : CppCond} {body : CppStmt}
    (prefixes : ∀ n : Nat, ∃ σn : State,
      WhilePrefix n σ cond body σn) :
    LoopBehaviorSource σ cond body :=
  .divergent (.forever prefixes)

/-- A behavior source classifies the while statement as finite or divergent. -/
def classification
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorSource σ cond body) :
    StmtClassified σ (.whileStmt cond body) :=
  match h with
  | .finite trace => trace.classification
  | .divergent trace => trace.classification

end LoopBehaviorSource

end Semantics
end Cpp3
