import CppFormalization.Cpp4.Boundary.Transport.Switch.Suffix
import CppFormalization.Cpp4.Boundary.Function
import CppFormalization.Cpp4.Resource.Transport.Surface

/-!
# CppFormalization.Cpp4.Boundary.Transport.Function

Boundary transport for typed surface function bodies and internal definitions.
-/

namespace Cpp4

/-- Transport from one typed function-body boundary to another. -/
structure FunctionBodyBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {sig sig' : FunctionSig} {body body' : StmtBlock}
    (before : FunctionBodyTyping sig body)
    (after : FunctionBodyTyping sig' body') : Type where
  transport : SurfaceBlockTransport χ χ' σ σ' eff before.demand after.demand

namespace FunctionBodyBoundaryTransport

/-- Apply function-body-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {sig sig' : FunctionSig} {body body' : StmtBlock}
    {before : FunctionBodyTyping sig body}
    {after : FunctionBodyTyping sig' body'}
    (b : FunctionBodyBoundary χ σ before)
    (t : FunctionBodyBoundaryTransport χ χ' σ σ' eff before after) :
    FunctionBodyBoundary χ' σ' after where
  demandsSatisfied := surface_block_transport b.demandsSatisfied t.transport

end FunctionBodyBoundaryTransport

/-- Transport from one internal-function boundary to another internal-function boundary. -/
structure InternalFunctionBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {d d' : InternalFunctionDef}
    (before : InternalFunctionTyping d)
    (after : InternalFunctionTyping d') : Type where
  bodyTransport : FunctionBodyBoundaryTransport χ χ' σ σ' eff before.bodyTyping after.bodyTyping

namespace InternalFunctionBoundaryTransport

/-- Apply internal-function-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {d d' : InternalFunctionDef}
    {before : InternalFunctionTyping d}
    {after : InternalFunctionTyping d'}
    (b : InternalFunctionBoundary χ σ before)
    (t : InternalFunctionBoundaryTransport χ χ' σ σ' eff before after) :
    InternalFunctionBoundary χ' σ' after where
  bodyBoundary := FunctionBodyBoundaryTransport.apply b.bodyBoundary t.bodyTransport

end InternalFunctionBoundaryTransport

end Cpp4
