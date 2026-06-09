import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Divergent

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Split

Split construction of the loop engine from finite and divergent cases.

The final loop-engine theorem should not pretend that every safe loop is finite,
and it should not restrict divergence to the forever-reentry case.  A lower
classification proof must choose one of the semantic cases:

* finite: a derivation-height indexed big-step while derivation;
* divergent: body divergence during a true-guard iteration, or forever reentry.

This file combines those separately-packaged cases into the existing
`LoopSafetyStepCoinductionTheorem` interface.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- The split semantic classification case for a safe while loop. -/
inductive LoopEngineCase
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | finite :
      FiniteLoopEngineCase Γ Γc σ cond body →
        LoopEngineCase Γ Γc σ cond body
  | divergent :
      DivergentLoopEngineCase Γ Γc σ cond body →
        LoopEngineCase Γ Γc σ cond body

namespace LoopEngineCase

/-- Convert the selected finite/divergent case into loop-classification evidence. -/
def evidence
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopClassificationEvidence σ cond body :=
  match h with
  | .finite hfinite => hfinite.evidence
  | .divergent hdivergent => hdivergent.evidence

/-- Convert the selected finite/divergent case into the loop-engine classification
package consumed by `Instantiate.LoopClassification`. -/
def classification
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionClassification
      Γ Γc σ cond body :=
  match h with
  | .finite hfinite => hfinite.classification
  | .divergent hdivergent => hdivergent.classification

/-- Direct closed while soundness from the selected finite/divergent loop-engine case. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopEngineCase Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  match h with
  | .finite hfinite => hfinite.closedSoundness
  | .divergent hdivergent => hdivergent.closedSoundness

end LoopEngineCase

/-- Lower-layer split theorem for loop-engine construction.

A proof of this theorem is where the real finite/divergent classification work
belongs.  It consumes a concrete while-entry boundary and returns the guard/body
loop-safety environment together with exactly one semantic classification case. -/
structure LoopEngineCaseSplitTheorem : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopEngineCase Γ Γc σ cond body

/-- Build the existing loop-engine theorem from a finite/divergent case split. -/
def loopSafetyStepCoinductionTheorem_of_caseSplit
    (C : LoopEngineCaseSplitTheorem) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem where
  classify := by
    intro Γ σ cond body boundary
    rcases C.classify boundary with ⟨Γc, selected⟩
    exact ⟨Γc, selected.classification⟩

end LoopEngine
end Derive
end Soundness
end Cpp3
