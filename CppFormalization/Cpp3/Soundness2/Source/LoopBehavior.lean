import CppFormalization.Cpp3.Soundness2.Source.ScopeExit
import CppFormalization.Cpp3.Semantics.Kernel.WhileTrace

/-!
# CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

Source vocabulary for while-loop behavior.

The finite/divergent while trace vocabulary is now lower-level semantics in
`Semantics.Kernel.WhileTrace`.  Soundness2 only keeps the boundary-facing loop
behavior certificate: a while boundary must expose a condition boundary, loop
safety surface, and one semantic behavior explanation.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Compatibility alias for the lower semantic while reentry-step trace. -/
abbrev LoopReentryStep (σ : State) (cond : CppCond) (body : CppStmt) : State → Type :=
  Semantics.LoopReentryStep σ cond body

/-- Compatibility alias for lower finite while traces. -/
abbrev FiniteLoopTrace (cond : CppCond) (body : CppStmt) :
    State → CtrlResult → State → Type :=
  Semantics.FiniteLoopTrace cond body

/-- Compatibility alias for lower divergent while traces. -/
abbrev DivergentLoopTrace (σ : State) (cond : CppCond) (body : CppStmt) : Type :=
  Semantics.DivergentLoopTrace σ cond body

/-- Compatibility alias for lower while behavior explanations. -/
abbrev LoopBehaviorSource (σ : State) (cond : CppCond) (body : CppStmt) : Type :=
  Semantics.LoopBehaviorSource σ cond body

/-- Loop behavior certificate with visible safety surfaces.

Classification is derived from the lower semantic `behavior`. -/
structure LoopBehaviorCertificate
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  behavior : Semantics.LoopBehaviorSource σ cond body

namespace LoopBehaviorCertificate

/-- Project the closed statement soundness target for the while statement. -/
def closedWhileSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorCertificate Γ Γc σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  h.behavior.classification

end LoopBehaviorCertificate

/-- Source theorem for producing loop behavior certificates from while boundaries. -/
structure LoopBehaviorCertificateTheorem : Type where
  certify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopBehaviorCertificate Γ Γc σ cond body

end Source
end Soundness2
end Cpp3
