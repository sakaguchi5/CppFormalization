import CppFormalization.Cpp3.Soundness.Instantiate.LoopClassification
import CppFormalization.Cpp3.SafetyFragment.Loop

/-!
# CppFormalization.Cpp3.Soundness.Instantiate.LoopEngine

Constructing `LoopClassificationTheorem` from loop-safety plus an explicit
finite/divergent classification engine.

The previous layer named the final while obligation as a
`LoopClassificationTheorem`.  This file refines that surface once more: the loop
classification theorem is obtained from a C++-facing loop-safety fragment plus an
explicit classification witness.

The witness has two honest cases:

* a finite big-step loop derivation, recorded with a derivation-height/step index;
* an infinite loop divergence witness, recorded coinductively through arbitrary
  finite prefixes (`WhilePrefix`) and consumed by `StmtDiv.whileForever`.

This file still does not prove that every safe loop has one of these witnesses.
That is the next lower-layer proof obligation.  What it does prove is the exact
bridge requested here:

`LoopSafetyFragment + step / derivation-height / coinduction -> LoopClassificationTheorem`.
-/

namespace Cpp3
namespace Soundness
namespace Instantiate
namespace LoopClassification

/-- Finite loop classification by an actual big-step derivation.

`derivationHeight` is the explicit step/height index that lower proof files can
use as the decreasing object when constructing this witness.  Once the finite
big-step derivation itself is present, closed statement soundness follows by the
left side of `StmtClassified`.
-/
structure FiniteLoopStepClassification
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  derivationHeight : Nat
  result : CtrlResult
  post : State
  step : Semantics.BigStepStmt σ (.whileStmt cond body) result post

namespace FiniteLoopStepClassification

/-- Project finite loop classification as closed statement soundness. -/
def closedSoundness
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : FiniteLoopStepClassification σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  Or.inl ⟨h.result, h.post, h.step⟩

end FiniteLoopStepClassification

/-- Infinite loop classification by the coinductive/divergence side.

The kernel's `whileForever` constructor classifies a loop as divergent when every
finite prefix length can be executed.  This is the C++-natural non-termination
case: the loop keeps re-entering without producing unclassified stuckness.
-/
structure CoinductiveLoopDivergence
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  prefixes : ∀ n : Nat, ∃ σn : State, Semantics.WhilePrefix n σ cond body σn

namespace CoinductiveLoopDivergence

/-- Project coinductive loop divergence as closed statement soundness. -/
def closedSoundness
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : CoinductiveLoopDivergence σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  Or.inr (Semantics.StmtDiv.whileForever h.prefixes)

end CoinductiveLoopDivergence

/-- The two semantic ways a safe while-loop can be classified.

The finite case is intended to be built by induction on a step/derivation-height
measure.  The infinite case is intended to be built by guarded/coinductive
prefix production.
-/
inductive LoopClassificationEvidence
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | finite :
      FiniteLoopStepClassification σ cond body →
        LoopClassificationEvidence σ cond body
  | infinite :
      CoinductiveLoopDivergence σ cond body →
        LoopClassificationEvidence σ cond body

namespace LoopClassificationEvidence

/-- Consume either finite or divergent loop evidence as closed statement soundness. -/
def closedSoundness
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopClassificationEvidence σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  match h with
  | .finite h_finite => h_finite.closedSoundness
  | .infinite h_infinite => h_infinite.closedSoundness

end LoopClassificationEvidence

/-- Loop-safety plus the semantic classification engine at a concrete entry.

This package keeps the C++ safety side visible instead of hiding it inside a raw
closed-soundness proof.  The `condition` field exposes the guard-entry boundary;
`loopSafety` records the guard-preservation/backedge/replay obligations; and
`evidence` records the finite-step or coinductive classification witness.
-/
structure LoopSafetyStepCoinductionClassification
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  evidence : LoopClassificationEvidence σ cond body

namespace LoopSafetyStepCoinductionClassification

/-- Project the closed while soundness carried by the loop engine package. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopSafetyStepCoinductionClassification Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.evidence.closedSoundness

end LoopSafetyStepCoinductionClassification

/-- Lower-layer theorem surface for constructing loop classification from safety.

A later proof file should consume the actual lower-layer facts and produce this
object.  The existential `Γc` is deliberate: the loop condition may refine the
runtime/static environment used for the body and backedge reasoning.
-/
structure LoopSafetyStepCoinductionTheorem : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopSafetyStepCoinductionClassification Γ Γc σ cond body

/-- Build the existing loop-classification theorem from safety + step/coinduction.

This is the bridge from the C++-facing loop engine to the previous
`LoopClassificationTheorem` interface.
-/
def loopClassificationTheorem_of_stepCoinduction
    (C : LoopSafetyStepCoinductionTheorem) :
    LoopClassificationTheorem where
  classify := by
    intro Γ σ cond body boundary
    rcases C.classify boundary with ⟨_Γc, classified⟩
    exact {
      boundary := boundary
      sound := classified.closedSoundness
    }

/-- Direct closed-while theorem from loop safety plus step/coinduction. -/
theorem closedWhileSoundness_of_stepCoinduction
    (C : LoopSafetyStepCoinductionTheorem)
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.whileStmt cond body)) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  closedWhileSoundness_of_loopClassification
    (loopClassificationTheorem_of_stepCoinduction C)
    boundary

end LoopClassification
end Instantiate
end Soundness
end Cpp3
