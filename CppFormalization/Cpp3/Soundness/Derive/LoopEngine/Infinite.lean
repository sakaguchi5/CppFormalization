import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Divergent

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Infinite

Compatibility wrapper for the old forever-only infinite loop-engine case.

The main divergent side now lives in `LoopEngine.Divergent`.  This file keeps the
old `InfiniteLoopEngineCase` name available as a thin wrapper for the
`whileForever` subcase, so existing imports do not immediately break.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- Legacy forever-only infinite loop-engine case.

Prefer `DivergentLoopEngineCase` for new code: it also covers divergence inside a
true-guard body evaluation. -/
structure InfiniteLoopEngineCase
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  divergence : Instantiate.LoopClassification.CoinductiveLoopDivergence σ cond body

namespace InfiniteLoopEngineCase

/-- Convert the legacy forever-only case into the general divergent case. -/
def toDivergent
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : InfiniteLoopEngineCase Γ Γc σ cond body) :
    DivergentLoopEngineCase Γ Γc σ cond body where
  condition := h.condition
  loopSafety := h.loopSafety
  divergence := Instantiate.LoopClassification.DivergentLoopClassification.forever h.divergence

/-- Convert the legacy infinite case into loop-classification evidence. -/
def evidence
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : InfiniteLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopClassificationEvidence σ cond body :=
  h.toDivergent.evidence

/-- Convert the legacy infinite case into the loop-engine classification package. -/
def classification
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : InfiniteLoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionClassification
      Γ Γc σ cond body :=
  h.toDivergent.classification

/-- Direct closed while soundness from the legacy infinite case. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : InfiniteLoopEngineCase Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.toDivergent.closedSoundness

end InfiniteLoopEngineCase

end LoopEngine
end Derive
end Soundness
end Cpp3
