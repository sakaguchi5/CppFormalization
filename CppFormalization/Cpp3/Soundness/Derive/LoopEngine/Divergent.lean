import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Finitary

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Divergent

Divergent-side construction package for the loop engine.

This replaces the previous forever-only `Infinite` side.  A C++ while-loop can
diverge in at least two semantically different ways:

* the guard is true and the body diverges before completing the current iteration;
* the loop completes arbitrarily long normal/continue prefixes, consumed by
  `StmtDiv.whileForever`.

Both are genuine while divergence, so the loop-engine split should expose a
`divergent` side rather than an `infinite` side.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- Divergent loop-engine case.

C++ reading: at this while-entry boundary, the loop does not produce a finite
result.  It either diverges inside a true-guard body evaluation, or it keeps
re-entering forever. -/
structure DivergentLoopEngineCase
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  divergence : Instantiate.LoopClassification.DivergentLoopClassification σ cond body

namespace DivergentLoopEngineCase

/-- Convert the divergent case into loop-classification evidence. -/
def evidence
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : DivergentLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopClassificationEvidence σ cond body :=
  Instantiate.LoopClassification.LoopClassificationEvidence.divergent h.divergence

/-- Convert the divergent case into the loop-engine classification package consumed
by `Instantiate.LoopClassification`. -/
def classification
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : DivergentLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionClassification
      Γ Γc σ cond body where
  condition := h.condition
  loopSafety := h.loopSafety
  evidence := h.evidence

/-- Direct closed while soundness from the divergent loop-engine case. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : DivergentLoopEngineCase Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.divergence.closedSoundness

end DivergentLoopEngineCase

end LoopEngine
end Derive
end Soundness
end Cpp3
