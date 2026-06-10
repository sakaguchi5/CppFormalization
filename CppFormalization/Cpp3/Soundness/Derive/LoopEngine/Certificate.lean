import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.TraceToClassification

/-!
# CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Certificate

Certificate-driven loop progress split.

The previous `LoopEngineCaseSplitTheorem` surface is useful as a final adapter, but
it is too opaque as the next construction target if read as a boundary-only proof:
a while-entry boundary says that the loop can be entered safely; it does not, by
itself, decide whether an arbitrary C++ loop eventually reaches a finite exit or
runs forever.

This file makes the missing information explicit.  A lower layer supplies a
`LoopProgressCertificate`: visible guard/body loop-safety surfaces plus a finite
or divergent trace.  The existing trace-to-classification bridges then turn that
certificate into the finite/divergent loop-engine case consumed by the final
soundness surface.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LoopEngine

/-- Trace-level classification certificate for one concrete while entry.

C++ reading: for this loop entry, the program/proof side explains the loop either
by a finite execution trace or by a genuine divergence trace.  This is the part
that cannot be recovered from `Boundary.StmtBoundary` alone. -/
inductive LoopTraceCertificate
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | finite
      {σout : State} {r : CtrlResult}
      (trace : FiniteLoopTrace σ cond body r σout) :
      LoopTraceCertificate σ cond body
  | divergent
      (trace : DivergentLoopTrace σ cond body) :
      LoopTraceCertificate σ cond body

namespace LoopTraceCertificate

/-- Convert a trace certificate, plus visible loop-safety surfaces, into the
split loop-engine case. -/
def toCase
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (h : LoopTraceCertificate σ cond body) :
    LoopEngineCase Γ Γc σ cond body :=
  match h with
  | .finite trace =>
      loopEngineCase_finite_of_trace condition loopSafety trace
  | .divergent trace =>
      loopEngineCase_divergent_of_trace condition loopSafety trace

/-- Direct closed while soundness from the trace certificate. -/
def closedSoundness
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopTraceCertificate σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  match h with
  | .finite trace =>
      closedWhileSoundness_of_finiteTrace trace
  | .divergent trace =>
      closedWhileSoundness_of_divergentTrace trace

end LoopTraceCertificate

/-- Certificate package for the loop-progress split.

C++ reading: a safe while-entry boundary contributes the guard boundary and the
safe-reentry obligations, but the finite-vs-divergent explanation is carried by
`trace`.  This keeps the safety contract separate from termination/divergence
classification. -/
structure LoopProgressCertificate
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  trace : LoopTraceCertificate σ cond body

namespace LoopProgressCertificate

/-- Convert the certificate package into the final finite/divergent loop-engine
case. -/
def toCase
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopProgressCertificate Γ Γc σ cond body) :
    LoopEngineCase Γ Γc σ cond body :=
  LoopTraceCertificate.toCase h.condition h.loopSafety h.trace

/-- Convert the certificate package into the classification package consumed by
`Instantiate.LoopClassification`. -/
def classification
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopProgressCertificate Γ Γc σ cond body) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionClassification
      Γ Γc σ cond body :=
  h.toCase.classification

/-- Direct closed while soundness from the certificate package. -/
def closedSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopProgressCertificate Γ Γc σ cond body) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  h.trace.closedSoundness

end LoopProgressCertificate

/-- Certificate-driven lower-layer theorem surface for while progress.

This is the intended construction target for the next layer.  The theorem still
starts from a concrete while-entry boundary, but it must return an explicit
certificate explaining the finite/divergent behavior.  In other words, the
classification evidence is no longer hidden inside a boundary-only split. -/
structure LoopProgressCertificateTheorem : Type where
  certify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopProgressCertificate Γ Γc σ cond body

/-- Compatibility adapter: a certificate-driven theorem induces the older
finite/divergent case-split surface. -/
def loopEngineCaseSplitTheorem_of_progressCertificate
    (C : LoopProgressCertificateTheorem) :
    LoopEngineCaseSplitTheorem where
  classify := by
    intro Γ σ cond body boundary
    rcases C.certify boundary with ⟨Γc, cert⟩
    exact ⟨Γc, cert.toCase⟩

/-- Build the loop-classification theorem directly from a certificate-driven
progress theorem. -/
def loopSafetyStepCoinductionTheorem_of_progressCertificate
    (C : LoopProgressCertificateTheorem) :
    Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem :=
  loopSafetyStepCoinductionTheorem_of_caseSplit
    (loopEngineCaseSplitTheorem_of_progressCertificate C)

end LoopEngine
end Derive
end Soundness
end Cpp3
