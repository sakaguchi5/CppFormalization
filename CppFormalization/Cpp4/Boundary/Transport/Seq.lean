import CppFormalization.Cpp4.Boundary.Transport.Block
import CppFormalization.Cpp4.Semantics.Effect.Plan

/-!
# CppFormalization.Cpp4.Boundary.Transport.Seq

Sequential ControlPlan transport vocabulary.

The key C++ reading is: after the head plan finishes normally, the tail boundary
must still hold in the post-state.  The concrete preservation proof is supplied
by the Resource.Transport layer.
-/

namespace Cpp4

/-- Transport certificate for the tail of a sequence after a normal head step. -/
structure SeqTailBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {tail tail' : ControlPlan}
    (beforeTail : PlanTyping Γ κ tail) (afterTail : PlanTyping Γ' κ' tail') : Type where
  tailTransport : PlanBoundaryTransport χ χ' σ σ' eff beforeTail afterTail

namespace SeqTailBoundaryTransport

/-- Apply a seq-tail transport certificate. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {tail tail' : ControlPlan}
    {beforeTail : PlanTyping Γ κ tail} {afterTail : PlanTyping Γ' κ' tail'}
    (bTail : PlanBoundary χ σ beforeTail)
    (t : SeqTailBoundaryTransport χ χ' σ σ' eff beforeTail afterTail) :
    PlanBoundary χ' σ' afterTail :=
  PlanBoundaryTransport.apply bTail t.tailTransport

end SeqTailBoundaryTransport

/-- A normal head execution together with tail-boundary preservation. -/
structure SeqNormalContinuationBoundary
    (χ χ' : DemandContext) (kχ : KernelContext)
    (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {head tail tail' : ControlPlan}
    (headStep : BigStepPlanWithEffect kχ σ head .normal σ')
    (beforeTail : PlanTyping Γ κ tail) (afterTail : PlanTyping Γ' κ' tail') : Type where
  effectMatches : headStep.trace.effect = eff
  tailTransport : SeqTailBoundaryTransport χ χ' σ σ' eff beforeTail afterTail

end Cpp4
