import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Finitary

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Infinite

Infinite-side construction package for the loop engine.

The infinite case is not a failed finite proof.  It is the C++-natural divergent
case: the while statement keeps completing true-condition normal/continue prefixes
for every finite length.  The semantics kernel consumes exactly this witness via
`StmtDiv.whileForever`.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- Infinite loop-engine case.

C++ reading: the loop is safe to re-enter for arbitrarily many completed
iterations, so the whole while statement is classified by divergence rather than
by a finite big-step result. -/
structure InfiniteLoopEngineCase
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  divergence : Instantiate.LoopClassification.CoinductiveLoopDivergence σ cond body

namespace InfiniteLoopEngineCase

/-- Convert the infinite case into loop-classification evidence. -/
def evidence
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : InfiniteLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopClassificationEvidence σ cond body :=
  Instantiate.LoopClassification.LoopClassificationEvidence.infinite h.divergence

/-- Convert the infinite case into the loop-engine classification package consumed
by `Instantiate.LoopClassification`. -/
def classification
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : InfiniteLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionClassification
      Γ Γc σ cond body where
  condition := h.condition
  loopSafety := h.loopSafety
  evidence := h.evidence

/-- Direct closed while soundness from the infinite loop-engine case. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : InfiniteLoopEngineCase Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.divergence.closedSoundness

end InfiniteLoopEngineCase

end LoopEngine
end Derive
end Soundness
end Cpp3
