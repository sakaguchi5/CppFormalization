import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Infinite

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Split

Split construction of the loop engine from finite and infinite cases.

The final loop-engine theorem should not pretend that every safe loop is finite,
and it should not pretend that every safe loop diverges.  A lower classification
proof must choose one of the two semantic cases:

* finite: a derivation-height indexed big-step while derivation;
* infinite: an arbitrary-prefix witness consumed by `StmtDiv.whileForever`.

This file combines those two separately-packaged cases into the existing
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
  | infinite :
      InfiniteLoopEngineCase Γ Γc σ cond body →
        LoopEngineCase Γ Γc σ cond body

namespace LoopEngineCase

/-- Convert the selected finite/infinite case into loop-classification evidence. -/
def evidence
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopClassificationEvidence σ cond body :=
  match h with
  | .finite hfinite => hfinite.evidence
  | .infinite hinfinite => hinfinite.evidence

/-- Convert the selected finite/infinite case into the loop-engine classification
package consumed by `Instantiate.LoopClassification`. -/
def classification
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopEngineCase Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionClassification
      Γ Γc σ cond body :=
  match h with
  | .finite hfinite => hfinite.classification
  | .infinite hinfinite => hinfinite.classification

/-- Direct closed while soundness from the selected finite/infinite loop-engine case. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopEngineCase Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  match h with
  | .finite hfinite => hfinite.closedSoundness
  | .infinite hinfinite => hinfinite.closedSoundness

end LoopEngineCase

/-- Lower-layer split theorem for loop-engine construction.

A proof of this theorem is where the real finite/infinite classification work
belongs.  It consumes a concrete while-entry boundary and returns the guard/body
loop-safety environment together with exactly one semantic classification case. -/
structure LoopEngineCaseSplitTheorem : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopEngineCase Γ Γc σ cond body

/-- Build the existing loop-engine theorem from a finite/infinite case split. -/
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
