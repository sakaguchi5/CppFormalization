import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.OneIteration

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Trace

Finite and divergent traces for while-loop classification.

A finite trace records finitely many normal/continue reentries followed by a
finite while exit.  A divergent trace records either body divergence during a
true-guard iteration or forever reentry through arbitrary finite prefixes.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- A finite while trace.

C++ reading: after a finite number of completed true-condition normal/continue
iterations, the loop reaches a finite exit: false guard, body `break`, or body
`return`. -/
inductive FiniteLoopTrace :
    State → CppCond → CppStmt → CtrlResult → State → Type where
  | falseExit
      {σ σc : State} {cond : CppCond} {body : CppStmt}
      (condFalse : Semantics.BigStepCond σ cond false σc) :
      FiniteLoopTrace σ cond body .normal σc
  | breakExit
      {σ σc σb : State} {cond : CppCond} {body : CppStmt}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyBreak : Semantics.BigStepStmt σc body .breakResult σb) :
      FiniteLoopTrace σ cond body .normal σb
  | returnExit
      {σ σc σb : State} {cond : CppCond} {body : CppStmt} {ov : Option Value}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyReturn : Semantics.BigStepStmt σc body (.returnResult ov) σb) :
      FiniteLoopTrace σ cond body (.returnResult ov) σb
  | reenter
      {σ σb σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
      (step : LoopReentryStep σ cond body σb)
      (tail : FiniteLoopTrace σb cond body r σout) :
      FiniteLoopTrace σ cond body r σout

namespace FiniteLoopTrace

/-- Convert a finite trace into the corresponding while big-step derivation. -/
def bigStep
    {σ σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (h : FiniteLoopTrace σ cond body r σout) :
    Semantics.BigStepStmt σ (.whileStmt cond body) r σout :=
  match h with
  | .falseExit condFalse =>
      Semantics.BigStepStmt.whileFalse condFalse
  | .breakExit condTrue bodyBreak =>
      Semantics.BigStepStmt.whileBodyBreak condTrue bodyBreak
  | .returnExit condTrue bodyReturn =>
      Semantics.BigStepStmt.whileBodyReturn condTrue bodyReturn
  | .reenter step tail =>
      step.extendBigStep (bigStep tail)

/-- A concrete derivation-height/step index for the finite trace. -/
def derivationHeight
    {σ σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (h : FiniteLoopTrace σ cond body r σout) : Nat :=
  match h with
  | .falseExit _ => 1
  | .breakExit _ _ => 1
  | .returnExit _ _ => 1
  | .reenter _ tail => tail.derivationHeight + 1

/-- Convert a finite trace into the finite side of the loop engine. -/
def finiteClassification
    {σ σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (h : FiniteLoopTrace σ cond body r σout) :
    Instantiate.LoopClassification.FiniteLoopStepClassification σ cond body where
  derivationHeight := h.derivationHeight
  result := r
  post := σout
  step := h.bigStep

end FiniteLoopTrace

/-- A divergent while trace.

C++ reading: either a true-guard body diverges during the current iteration, or
the loop can complete arbitrarily long true-condition normal/continue prefixes. -/
inductive DivergentLoopTrace
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | bodyDiverges
      {σc : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyDiv : Semantics.StmtDiv σc body) :
      DivergentLoopTrace σ cond body
  | forever
      (prefixes : ∀ n : Nat, ∃ σn : State,
        Semantics.WhilePrefix n σ cond body σn) :
      DivergentLoopTrace σ cond body

namespace DivergentLoopTrace

/-- Convert a divergent trace into while divergence. -/
def stmtDiv
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : DivergentLoopTrace σ cond body) :
    Semantics.StmtDiv σ (.whileStmt cond body) :=
  match h with
  | .bodyDiverges condTrue bodyDiv =>
      Semantics.StmtDiv.whileBody condTrue bodyDiv
  | .forever prefixes =>
      Semantics.StmtDiv.whileForever prefixes

/-- Convert a divergent trace into the divergent side of the loop engine. -/
def divergentClassification
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : DivergentLoopTrace σ cond body) :
    Instantiate.LoopClassification.DivergentLoopClassification σ cond body :=
  match h with
  | .bodyDiverges condTrue bodyDiv =>
      Instantiate.LoopClassification.DivergentLoopClassification.bodyDiverges
        condTrue bodyDiv
  | .forever prefixes =>
      Instantiate.LoopClassification.DivergentLoopClassification.forever
        { prefixes := prefixes }

end DivergentLoopTrace

end LoopEngine
end Derive
end Soundness
end Cpp3
