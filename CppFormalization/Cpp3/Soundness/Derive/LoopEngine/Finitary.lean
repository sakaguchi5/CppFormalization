import CppFormalization.Cpp3.Soundness.Instantiate.LoopEngine

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Finitary

Finite-side construction package for the loop engine.

`Soundness.Instantiate.LoopEngine` already introduced the final loop-engine
surface consumed by `StepLoopFinal`.  This file separates the finite side of that
engine: a finite loop classification is an actual big-step derivation of the
whole while statement, together with its derivation-height/step index, plus the
loop-safety and guard-boundary surfaces that explain why this is a safe C++ loop
entry.

This file does not claim that every safe loop is finite.  It only packages the
finite case so the combined loop-engine split can choose it when the lower
semantic classification proof has produced a finite derivation.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- Finite loop-engine case.

C++ reading: at this while-entry boundary, the loop has a finite big-step route.
The finite semantic witness is kept separate from the safety surfaces: safety says
that the route is permitted; the finite witness says what actually happens. -/
structure FiniteLoopEngineCase
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  finite : Instantiate.LoopClassification.FiniteLoopStepClassification σ cond body

namespace FiniteLoopEngineCase

/-- Convert the finite case into loop-classification evidence. -/
def evidence
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : FiniteLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopClassificationEvidence σ cond body :=
  Instantiate.LoopClassification.LoopClassificationEvidence.finite h.finite

/-- Convert the finite case into the loop-engine classification package consumed
by `Instantiate.LoopClassification`. -/
def classification
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : FiniteLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionClassification
      Γ Γc σ cond body where
  condition := h.condition
  loopSafety := h.loopSafety
  evidence := h.evidence

/-- Direct closed while soundness from the finite loop-engine case. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : FiniteLoopEngineCase Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.finite.closedSoundness

end FiniteLoopEngineCase

end LoopEngine
end Derive
end Soundness
end Cpp3
