import CppFormalization.Cpp3.Soundness.Structural.Mutual

/-!
# CppFormalization.Cpp3.Soundness.Instantiate.LoopClassification

Loop-classification instantiation for while reentry soundness.

At this point all local-control and scope-exit provider slots have been reduced
away.  The only remaining same-syntax problem is while reentry: after a
normal/continue backedge the next program point is again the same while statement
at a new state, so plain structural recursion cannot justify the classification.

This file names the needed C++ theorem surface as `LoopClassificationTheorem` and
turns it into the old `WhileReentrySoundnessProvider` by projecting the reentry
boundary carried by `Continuation.WhileReentryContinuation`.

The theorem is intentionally boundary-indexed.  Later files should construct it
from loop-safety invariants plus a step-index / derivation-height / coinductive
classification argument.  This file is only the bridge:

`LoopClassification theorem -> closed while soundness -> while reentry provider`.
-/

namespace Cpp3
namespace Soundness
namespace Instantiate
namespace LoopClassification

/-- A classified while-loop at a concrete entry boundary.

C++ reading: starting from this loop-entry boundary, the loop is already
classified as a statement: finite exit/break/return propagation and divergence
are all accounted for, so it cannot be an unclassified stuck state. -/
structure ClassifiedLoop
    (Γ : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  boundary : Boundary.StmtBoundary Γ σ (.whileStmt cond body)
  sound : ClosedStmtSoundness σ (.whileStmt cond body)

namespace ClassifiedLoop

/-- Project the closed statement soundness carried by a classified loop. -/
def closedSoundness
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : ClassifiedLoop Γ σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.sound

end ClassifiedLoop

/-- Lower-layer theorem surface for classifying a while loop.

This is the C++-facing loop theorem that should eventually be proved from:

* guard/body safety at the loop entry;
* body normal/continue backedge preservation;
* finite-route classification by induction on a step/derivation measure;
* infinite-route classification by guarded/coinductive divergence.

It is not a structural-recursion theorem over syntax.  The syntax is the same at
a reentry point, so the intended decreasing/guarded object lives in the loop
classification engine, not in `Structural.Mutual`. -/
structure LoopClassificationTheorem : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        ClassifiedLoop Γ σ cond body

/-- Closed while soundness obtained from the loop-classification theorem. -/
theorem closedWhileSoundness_of_loopClassification
    (C : LoopClassificationTheorem)
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.whileStmt cond body)) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  (C.classify boundary).closedSoundness

/-- Turn a loop-classification theorem into the old while-reentry provider.

A while reentry continuation already carries the boundary for the same while
statement at the reentry state.  The loop-classification theorem consumes exactly
that boundary. -/
def whileReentrySoundnessProvider_of_loopClassification
    (C : LoopClassificationTheorem) :
    Structural.WhileReentrySoundnessProvider where
  sound := by
    intro Γ Γc σ σreentry cond body Reentry cont
    exact closedWhileSoundness_of_loopClassification C cont.reentryBoundary

end LoopClassification
end Instantiate
end Soundness
end Cpp3
