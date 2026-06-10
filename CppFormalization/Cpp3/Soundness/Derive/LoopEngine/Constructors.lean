import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Certificate

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Constructors

Bottom-up constructors for the certificate-driven loop engine.

The earlier loop-engine files introduced the small semantic pieces:

* one-iteration outcomes and reentry steps;
* finite and divergent traces;
* trace-to-classification bridges;
* certificate-driven adapters into the final loop-engine surface.

This file fixes the construction direction.  It does not introduce another large
boundary-only theorem.  Instead it starts from the smallest C++ operational facts
(false guard, body break/return/divergence, normal/continue reentry, forever
prefixes), builds trace certificates, then builds progress certificates and the
existing loop-engine cases.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

namespace LoopReentryStep

/-- One normal body completion re-enters the same while statement. -/
def normalStep
    {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyStep : Semantics.BigStepStmt σc body .normal σb) :
    LoopReentryStep σ cond body σb :=
  LoopReentryStep.bodyNormal condTrue bodyStep

/-- One `continue` body completion re-enters the same while statement. -/
def continueStep
    {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyStep : Semantics.BigStepStmt σc body .continueResult σb) :
    LoopReentryStep σ cond body σb :=
  LoopReentryStep.bodyContinue condTrue bodyStep

end LoopReentryStep

namespace LoopTraceCertificate

/-- Package an already-built finite trace as a trace certificate. -/
def finiteOfTrace
    {σ σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (trace : FiniteLoopTrace σ cond body r σout) :
    LoopTraceCertificate σ cond body :=
  LoopTraceCertificate.finite trace

/-- Package an already-built divergent trace as a trace certificate. -/
def divergentOfTrace
    {σ : State} {cond : CppCond} {body : CppStmt}
    (trace : DivergentLoopTrace σ cond body) :
    LoopTraceCertificate σ cond body :=
  LoopTraceCertificate.divergent trace

/-- Build the finite certificate for the false-guard while exit. -/
def falseExit
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condFalse : Semantics.BigStepCond σ cond false σc) :
    LoopTraceCertificate σ cond body :=
  finiteOfTrace (FiniteLoopTrace.falseExit condFalse)

/-- Build the finite certificate for a true guard followed by body `break`. -/
def breakExit
    {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyBreak : Semantics.BigStepStmt σc body .breakResult σb) :
    LoopTraceCertificate σ cond body :=
  finiteOfTrace (FiniteLoopTrace.breakExit condTrue bodyBreak)

/-- Build the finite certificate for a true guard followed by body `return`. -/
def returnExit
    {σ σc σb : State} {cond : CppCond} {body : CppStmt} {ov : Option Value}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyReturn : Semantics.BigStepStmt σc body (.returnResult ov) σb) :
    LoopTraceCertificate σ cond body :=
  finiteOfTrace (FiniteLoopTrace.returnExit condTrue bodyReturn)

/-- Extend a finite tail certificate through one normal/continue reentry step. -/
def reenterFinite
    {σ σb σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (step : LoopReentryStep σ cond body σb)
    (tail : FiniteLoopTrace σb cond body r σout) :
    LoopTraceCertificate σ cond body :=
  finiteOfTrace (FiniteLoopTrace.reenter step tail)

/-- Build the divergent certificate for a true guard whose body diverges. -/
def bodyDiverges
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyDiv : Semantics.StmtDiv σc body) :
    LoopTraceCertificate σ cond body :=
  divergentOfTrace (DivergentLoopTrace.bodyDiverges condTrue bodyDiv)

/-- Build the divergent certificate for forever reentry, expressed by arbitrary
finite while prefixes. -/
def forever
    {σ : State} {cond : CppCond} {body : CppStmt}
    (prefixes : ∀ n : Nat, ∃ σn : State,
      Semantics.WhilePrefix n σ cond body σn) :
    LoopTraceCertificate σ cond body :=
  divergentOfTrace (DivergentLoopTrace.forever prefixes)

end LoopTraceCertificate

namespace LoopProgressCertificate

/-- Bottom-up progress certificate constructor from visible loop-safety surfaces
and a trace certificate. -/
def ofTraceCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : LoopTraceCertificate σ cond body) :
    LoopProgressCertificate Γ Γc σ cond body where
  condition := condition
  loopSafety := loopSafety
  trace := trace

/-- Progress certificate from an already-built finite trace. -/
def finiteOfTrace
    {Γ Γc : TypeEnv} {σ σout : State} {cond : CppCond} {body : CppStmt}
    {r : CtrlResult}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : FiniteLoopTrace σ cond body r σout) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.finiteOfTrace trace)

/-- Progress certificate from an already-built divergent trace. -/
def divergentOfTrace
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : DivergentLoopTrace σ cond body) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.divergentOfTrace trace)

/-- Progress certificate for the false-guard finite exit. -/
def falseExit
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condFalse : Semantics.BigStepCond σ cond false σc) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.falseExit condFalse)

/-- Progress certificate for a true guard followed by body `break`. -/
def breakExit
    {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyBreak : Semantics.BigStepStmt σc body .breakResult σb) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.breakExit condTrue bodyBreak)

/-- Progress certificate for a true guard followed by body `return`. -/
def returnExit
    {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    {ov : Option Value}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyReturn : Semantics.BigStepStmt σc body (.returnResult ov) σb) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.returnExit condTrue bodyReturn)

/-- Progress certificate obtained by extending a finite tail through one
normal/continue reentry step. -/
def reenterFinite
    {Γ Γc : TypeEnv} {σ σb σout : State} {cond : CppCond} {body : CppStmt}
    {r : CtrlResult}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (step : LoopReentryStep σ cond body σb)
    (tail : FiniteLoopTrace σb cond body r σout) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.reenterFinite step tail)

/-- Progress certificate for a true guard whose body diverges. -/
def bodyDiverges
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyDiv : Semantics.StmtDiv σc body) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.bodyDiverges condTrue bodyDiv)

/-- Progress certificate for forever reentry. -/
def forever
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (prefixes : ∀ n : Nat, ∃ σn : State,
      Semantics.WhilePrefix n σ cond body σn) :
    LoopProgressCertificate Γ Γc σ cond body :=
  ofTraceCertificate condition loopSafety
    (LoopTraceCertificate.forever prefixes)

end LoopProgressCertificate

namespace LoopEngineCase

/-- Build the final loop-engine case directly from visible loop-safety surfaces and
a trace certificate. -/
def ofTraceCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : LoopTraceCertificate σ cond body) :
    LoopEngineCase Γ Γc σ cond body :=
  trace.toCase condition loopSafety

/-- Build the final loop-engine case from the progress certificate package. -/
def ofProgressCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (cert : LoopProgressCertificate Γ Γc σ cond body) :
    LoopEngineCase Γ Γc σ cond body :=
  cert.toCase

end LoopEngineCase

/-- Build the certificate-driven theorem surface from a bottom-up certifier. -/
def loopProgressCertificateTheorem_of_certifier
    (certify :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopProgressCertificate Γ Γc σ cond body) :
    LoopProgressCertificateTheorem where
  certify := certify

/-- Compose a bottom-up certifier all the way to the final loop-classification
engine surface. -/
def loopSafetyStepCoinductionTheorem_of_certifier
    (certify :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopProgressCertificate Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem :=
  loopSafetyStepCoinductionTheorem_of_progressCertificate
    (loopProgressCertificateTheorem_of_certifier certify)

end LoopEngine
end Derive
end Soundness
end Cpp3
