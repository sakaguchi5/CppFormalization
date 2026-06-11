import CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

/-!
# CppFormalization.Cpp3.Soundness2.Realize.LoopBehavior

Realized loop-behavior layer for the closed-internal Soundness2 route.

`while` is not classified by local-control alone.  The final route first obtains
a loop-behavior certificate, and the statement classifier then uses that
certificate as the while case.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Lower realization source for a while behavior certificate. -/
structure LoopBehaviorComponentSource
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  behavior : Source.LoopBehaviorSource σ cond body

namespace LoopBehaviorComponentSource

/-- Convert lower loop-behavior components into the behavior certificate. -/
def toCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorComponentSource Γ Γc σ cond body) :
    Source.LoopBehaviorCertificate Γ Γc σ cond body where
  condition := h.condition
  loopSafety := h.loopSafety
  behavior := h.behavior

end LoopBehaviorComponentSource

/-- Build the loop-behavior theorem from a lower behavior-component certifier. -/
def loopBehaviorCertificateTheorem_of_componentTheorem
    (certify :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body) :
    Source.LoopBehaviorCertificateTheorem where
  certify := by
    intro Γ σ cond body boundary
    rcases certify boundary with ⟨Γc, source⟩
    exact ⟨Γc, source.toCertificate⟩

end Realize
end Soundness2
end Cpp3
