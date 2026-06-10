import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Constructors

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.BehaviorSource

Phase 2: behavior-source layer for the certificate-driven loop engine.

Phase 1 fixed the bottom-up construction route:

* small C++ operational facts;
* finite/divergent traces;
* trace certificates;
* progress certificates;
* final loop-engine cases.

This file adds the layer that explains *why* a particular loop supplies a trace
certificate.  It is deliberately not a case selector.  Each source constructor
carries the semantic evidence needed for its behavior:

* finite behavior carries a `FiniteLoopTrace`;
* body-divergence behavior carries a true guard and body divergence;
* forever behavior carries arbitrary finite while prefixes.

C++ reading: a good loop is not required to terminate.  It must instead provide a
behavior certificate explaining finite completion, divergence inside the body, or
productive forever reentry.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- Source-level behavior explanation for one concrete while entry.

This layer records the C++ reason that a loop can provide a trace certificate.
The finite side is a full finite trace, whose internal constructors are
false-guard exit, break exit, return exit, and finite reentry.  The divergent side
is either body divergence after a true guard, or productive forever reentry by
arbitrary finite prefixes. -/
inductive LoopBehaviorSource
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | finite
      {σout : State} {r : CtrlResult}
      (trace : FiniteLoopTrace σ cond body r σout) :
      LoopBehaviorSource σ cond body
  | bodyDiverges
      {σc : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyDiv : Semantics.StmtDiv σc body) :
      LoopBehaviorSource σ cond body
  | forever
      (prefixes : ∀ n : Nat, ∃ σn : State,
        Semantics.WhilePrefix n σ cond body σn) :
      LoopBehaviorSource σ cond body

namespace LoopBehaviorSource

/-- Package an already-built finite trace as a behavior source. -/
def finiteOfTrace
    {σ σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (trace : FiniteLoopTrace σ cond body r σout) :
    LoopBehaviorSource σ cond body :=
  LoopBehaviorSource.finite trace

/-- Build the finite behavior source for the false-guard while exit. -/
def falseExit
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condFalse : Semantics.BigStepCond σ cond false σc) :
    LoopBehaviorSource σ cond body :=
  finiteOfTrace (FiniteLoopTrace.falseExit condFalse)

/-- Build the finite behavior source for a true guard followed by body `break`. -/
def breakExit
    {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyBreak : Semantics.BigStepStmt σc body .breakResult σb) :
    LoopBehaviorSource σ cond body :=
  finiteOfTrace (FiniteLoopTrace.breakExit condTrue bodyBreak)

/-- Build the finite behavior source for a true guard followed by body `return`. -/
def returnExit
    {σ σc σb : State} {cond : CppCond} {body : CppStmt} {ov : Option Value}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyReturn : Semantics.BigStepStmt σc body (.returnResult ov) σb) :
    LoopBehaviorSource σ cond body :=
  finiteOfTrace (FiniteLoopTrace.returnExit condTrue bodyReturn)

/-- Extend a finite tail behavior through one normal/continue reentry step. -/
def reenterFinite
    {σ σb σout : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult}
    (step : LoopReentryStep σ cond body σb)
    (tail : FiniteLoopTrace σb cond body r σout) :
    LoopBehaviorSource σ cond body :=
  finiteOfTrace (FiniteLoopTrace.reenter step tail)

/-- Build the body-divergence behavior source.

C++ reading: the guard evaluates to true, and the body itself never returns from
that iteration. -/
def bodyDivergesOfEvidence
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyDiv : Semantics.StmtDiv σc body) :
    LoopBehaviorSource σ cond body :=
  LoopBehaviorSource.bodyDiverges condTrue bodyDiv

/-- Build the productive-forever behavior source.

C++ reading: for every finite number of iterations, the loop can execute that
many safe prefixes.  This is the shape used by game loops and event loops when
the model does not force an exit event. -/
def foreverOfPrefixes
    {σ : State} {cond : CppCond} {body : CppStmt}
    (prefixes : ∀ n : Nat, ∃ σn : State,
      Semantics.WhilePrefix n σ cond body σn) :
    LoopBehaviorSource σ cond body :=
  LoopBehaviorSource.forever prefixes

/-- Convert a behavior source into the trace certificate consumed by Phase 1. -/
def toTraceCertificate
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorSource σ cond body) :
    LoopTraceCertificate σ cond body :=
  match h with
  | .finite trace =>
      LoopTraceCertificate.finiteOfTrace trace
  | .bodyDiverges condTrue bodyDiv =>
      LoopTraceCertificate.bodyDiverges condTrue bodyDiv
  | .forever prefixes =>
      LoopTraceCertificate.forever prefixes

/-- Convert a behavior source plus visible loop surfaces into a progress certificate. -/
def toProgressCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (h : LoopBehaviorSource σ cond body) :
    LoopProgressCertificate Γ Γc σ cond body :=
  LoopProgressCertificate.ofTraceCertificate condition loopSafety
    (toTraceCertificate h)

/-- Convert a behavior source plus visible loop surfaces into the final loop case. -/
def toCase
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (h : LoopBehaviorSource σ cond body) :
    LoopEngineCase Γ Γc σ cond body :=
  (toProgressCertificate condition loopSafety h).toCase

/-- Direct closed while soundness from the behavior source. -/
def closedSoundness
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorSource σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  (toTraceCertificate h).closedSoundness

end LoopBehaviorSource

/-- Loop behavior certificate with the visible loop-entry safety surfaces.

`condition` and `loopSafety` are the safe-entry/reentry side.  `behavior` is the
finite/divergent explanation.  Keeping these fields separate prevents the
boundary from silently acting as a termination/divergence oracle. -/
structure LoopBehaviorCertificate
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  behavior : LoopBehaviorSource σ cond body

namespace LoopBehaviorCertificate

/-- Build a behavior certificate from visible loop surfaces and a behavior source. -/
def ofBehaviorSource
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (behavior : LoopBehaviorSource σ cond body) :
    LoopBehaviorCertificate Γ Γc σ cond body where
  condition := condition
  loopSafety := loopSafety
  behavior := behavior

/-- Project the trace certificate explained by this behavior certificate. -/
def toTraceCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorCertificate Γ Γc σ cond body) :
    LoopTraceCertificate σ cond body :=
  h.behavior.toTraceCertificate

/-- Convert a behavior certificate into the Phase-1 progress certificate. -/
def toProgressCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorCertificate Γ Γc σ cond body) :
    LoopProgressCertificate Γ Γc σ cond body :=
  LoopProgressCertificate.ofTraceCertificate h.condition h.loopSafety
    h.toTraceCertificate

/-- Convert a behavior certificate into the final finite/divergent loop-engine case. -/
def toCase
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorCertificate Γ Γc σ cond body) :
    LoopEngineCase Γ Γc σ cond body :=
  h.toProgressCertificate.toCase

/-- Direct closed while soundness from the behavior certificate. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorCertificate Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.behavior.closedSoundness

/-- Behavior certificate for an already-built finite trace. -/
def finiteOfTrace
    {Γ Γc : TypeEnv} {σ σout : State} {cond : CppCond} {body : CppStmt}
    {r : CtrlResult}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (trace : FiniteLoopTrace σ cond body r σout) :
    LoopBehaviorCertificate Γ Γc σ cond body :=
  ofBehaviorSource condition loopSafety
    (LoopBehaviorSource.finiteOfTrace trace)

/-- Behavior certificate for the false-guard finite exit. -/
def falseExit
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condFalse : Semantics.BigStepCond σ cond false σc) :
    LoopBehaviorCertificate Γ Γc σ cond body :=
  ofBehaviorSource condition loopSafety
    (LoopBehaviorSource.falseExit condFalse)

/-- Behavior certificate for a true guard followed by body `break`. -/
def breakExit
    {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyBreak : Semantics.BigStepStmt σc body .breakResult σb) :
    LoopBehaviorCertificate Γ Γc σ cond body :=
  ofBehaviorSource condition loopSafety
    (LoopBehaviorSource.breakExit condTrue bodyBreak)

/-- Behavior certificate for a true guard followed by body `return`. -/
def returnExit
    {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    {ov : Option Value}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyReturn : Semantics.BigStepStmt σc body (.returnResult ov) σb) :
    LoopBehaviorCertificate Γ Γc σ cond body :=
  ofBehaviorSource condition loopSafety
    (LoopBehaviorSource.returnExit condTrue bodyReturn)

/-- Behavior certificate obtained by extending a finite tail through one
normal/continue reentry step. -/
def reenterFinite
    {Γ Γc : TypeEnv} {σ σb σout : State} {cond : CppCond} {body : CppStmt}
    {r : CtrlResult}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (step : LoopReentryStep σ cond body σb)
    (tail : FiniteLoopTrace σb cond body r σout) :
    LoopBehaviorCertificate Γ Γc σ cond body :=
  ofBehaviorSource condition loopSafety
    (LoopBehaviorSource.reenterFinite step tail)

/-- Behavior certificate for true guard plus body divergence. -/
def bodyDiverges
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyDiv : Semantics.StmtDiv σc body) :
    LoopBehaviorCertificate Γ Γc σ cond body :=
  ofBehaviorSource condition loopSafety
    (LoopBehaviorSource.bodyDivergesOfEvidence condTrue bodyDiv)

/-- Behavior certificate for productive forever reentry. -/
def forever
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (prefixes : ∀ n : Nat, ∃ σn : State,
      Semantics.WhilePrefix n σ cond body σn) :
    LoopBehaviorCertificate Γ Γc σ cond body :=
  ofBehaviorSource condition loopSafety
    (LoopBehaviorSource.foreverOfPrefixes prefixes)

end LoopBehaviorCertificate

/-- Behavior-driven theorem surface for supplying loop certificates.

This is the Phase-2 construction target.  It still starts from the concrete while
boundary because the final soundness theorem is boundary-indexed, but the result
is no longer a raw progress certificate: it records the C++ behavior source that
justifies the finite/divergent trace. -/
structure LoopBehaviorCertificateTheorem : Type where
  certify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopBehaviorCertificate Γ Γc σ cond body

/-- Convert a behavior-driven theorem into the Phase-1 progress-certificate
theorem. -/
def loopProgressCertificateTheorem_of_behaviorCertificate
    (C : LoopBehaviorCertificateTheorem) :
    LoopProgressCertificateTheorem where
  certify := by
    intro Γ σ cond body boundary
    rcases C.certify boundary with ⟨Γc, behaviorCert⟩
    exact ⟨Γc, behaviorCert.toProgressCertificate⟩

/-- Build the loop-classification theorem from a behavior-driven certificate
theorem. -/
def loopSafetyStepCoinductionTheorem_of_behaviorCertificate
    (C : LoopBehaviorCertificateTheorem) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem :=
  loopSafetyStepCoinductionTheorem_of_progressCertificate
    (loopProgressCertificateTheorem_of_behaviorCertificate C)

/-- Build a behavior-certificate theorem from a bottom-up certifier. -/
def loopBehaviorCertificateTheorem_of_certifier
    (certify :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorCertificate Γ Γc σ cond body) :
    LoopBehaviorCertificateTheorem where
  certify := certify

/-- Compose a bottom-up behavior certifier all the way to the final loop engine
surface. -/
def loopSafetyStepCoinductionTheorem_of_behaviorCertifier
    (certify :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorCertificate Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem :=
  loopSafetyStepCoinductionTheorem_of_behaviorCertificate
    (loopBehaviorCertificateTheorem_of_certifier certify)

end LoopEngine
end Derive
end Soundness
end Cpp3
