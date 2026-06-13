import CppFormalization.Cpp4.Boundary.Surface
import CppFormalization.Cpp4.Typing.Judgment.Surface.Function

/-!
# CppFormalization.Cpp4.Boundary.Function

Runtime boundaries for typed surface function bodies and internal definitions.
-/

namespace Cpp4

/-- A typed function body is enterable when the demand of its typed surface block is satisfied. -/
structure FunctionBodyBoundary
    (χ : DemandContext) (σ : State) {sig : FunctionSig} {body : StmtBlock}
    (h : FunctionBodyTyping sig body) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ (FunctionBodyTyping.demand h).demands

namespace FunctionBodyBoundary

/-- Repackage a function-body boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {sig : FunctionSig} {body : StmtBlock}
    {h : FunctionBodyTyping sig body} (b : FunctionBodyBoundary χ σ h) :
    DemandBoundary χ σ (FunctionBodyTyping.demand h).demands where
  satisfied := b.demandsSatisfied

/-- Build a function-body boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {sig : FunctionSig} {body : StmtBlock}
    {h : FunctionBodyTyping sig body}
    (b : DemandBoundary χ σ (FunctionBodyTyping.demand h).demands) :
    FunctionBodyBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Surface block boundary induced by a function-body boundary. -/
def bodyBlockBoundary {χ : DemandContext} {σ : State} {sig : FunctionSig} {body : StmtBlock}
    {h : FunctionBodyTyping sig body} (b : FunctionBodyBoundary χ σ h) :
    SurfaceBlockBoundary χ σ h.bodyTyping where
  demandsSatisfied := b.demandsSatisfied

end FunctionBodyBoundary

/-- A typed internal function definition is enterable when its body boundary holds. -/
structure InternalFunctionBoundary
    (χ : DemandContext) (σ : State) {d : InternalFunctionDef}
    (h : InternalFunctionTyping d) : Type where
  bodyBoundary : FunctionBodyBoundary χ σ h.bodyTyping

namespace InternalFunctionBoundary

/-- Formation evidence stored by the internal-function typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {d : InternalFunctionDef}
    {h : InternalFunctionTyping d} (_b : InternalFunctionBoundary χ σ h) :
    h.formation :=
  h.evidence

end InternalFunctionBoundary

end Cpp4
