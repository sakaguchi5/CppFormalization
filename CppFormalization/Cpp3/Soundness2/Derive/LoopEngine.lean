import CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

/-!
# CppFormalization.Cpp3.Soundness2.Derive.LoopEngine

Loop-engine derivations from Soundness2 loop behavior certificates.
-/

namespace Cpp3
namespace Soundness2
namespace Derive

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
