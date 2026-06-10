import CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

/-!
# CppFormalization.Cpp3.Soundness2.Derive.LoopEngine

Loop-engine derivations from Soundness2 loop behavior sources.
-/

namespace Cpp3
namespace Soundness2
namespace Derive

/-- Finite loop traces classify the while statement by finite big-step execution. -/
def finiteLoopTrace_classification
    {cond : CppCond} {body : CppStmt} {σ σout : State} {r : CtrlResult}
    (trace : Source.FiniteLoopTrace cond body σ r σout) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  trace.classification

/-- Divergent loop traces classify the while statement by divergence. -/
def divergentLoopTrace_classification
    {σ : State} {cond : CppCond} {body : CppStmt}
    (trace : Source.DivergentLoopTrace σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  trace.classification

/-- Behavior sources classify the while statement. -/
def loopBehaviorSource_classification
    {σ : State} {cond : CppCond} {body : CppStmt}
    (behavior : Source.LoopBehaviorSource σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  behavior.classification

/-- Derive while statement classification from a loop behavior certificate. -/
def closedWhileSoundness_of_behaviorCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (cert : Source.LoopBehaviorCertificate Γ Γc σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  cert.closedWhileSoundness

/-- Project the Soundness2 loop-behavior theorem surface. -/
def loopBehaviorCertificateTheorem
    (source : Source.LoopBehaviorCertificateTheorem) :
    Source.LoopBehaviorCertificateTheorem :=
  source

end Derive
end Soundness2
end Cpp3
