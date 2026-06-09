import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Trace
import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Split

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.TraceToClassification

Trace-to-loop-engine classification bridges.

This file discharges the easy theoremized part of the loop-engine plan:
finite traces build finite big-step loop classifications, and divergent traces
build divergent loop classifications.  The remaining hard theorem is the future
case split producing one of these traces from lower-layer progress facts.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- Build a finite loop-engine case from a finite loop trace plus the visible loop
safety surfaces. -/
def finiteLoopEngineCase_of_trace
    {Γ Γc : TypeEnv} {σ σout : State} {cond : CppCond} {body : CppStmt}
    {r : CtrlResult}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : FiniteLoopTrace σ cond body r σout) :
    FiniteLoopEngineCase Γ Γc σ cond body where
  condition := condition
  loopSafety := loopSafety
  finite := trace.finiteClassification

/-- Build a divergent loop-engine case from a divergent loop trace plus the visible
loop safety surfaces. -/
def divergentLoopEngineCase_of_trace
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : DivergentLoopTrace σ cond body) :
    DivergentLoopEngineCase Γ Γc σ cond body where
  condition := condition
  loopSafety := loopSafety
  divergence := trace.divergentClassification

/-- Finite trace to the split loop-engine case. -/
def loopEngineCase_finite_of_trace
    {Γ Γc : TypeEnv} {σ σout : State} {cond : CppCond} {body : CppStmt}
    {r : CtrlResult}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : FiniteLoopTrace σ cond body r σout) :
    LoopEngineCase Γ Γc σ cond body :=
  .finite (finiteLoopEngineCase_of_trace condition loopSafety trace)

/-- Divergent trace to the split loop-engine case. -/
def loopEngineCase_divergent_of_trace
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : DivergentLoopTrace σ cond body) :
    LoopEngineCase Γ Γc σ cond body :=
  .divergent (divergentLoopEngineCase_of_trace condition loopSafety trace)

/-- Direct finite-trace closed while soundness. -/
theorem closedWhileSoundness_of_finiteTrace
    {σ σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (trace : FiniteLoopTrace σ cond body r σout) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  trace.finiteClassification.closedSoundness

/-- Direct divergent-trace closed while soundness. -/
theorem closedWhileSoundness_of_divergentTrace
    {σ : State} {cond : CppCond} {body : CppStmt}
    (trace : DivergentLoopTrace σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  trace.divergentClassification.closedSoundness

end LoopEngine
end Derive
end Soundness
end Cpp3
