import CppFormalization.Cpp4.Boundary.Transport.Surface
import CppFormalization.Cpp4.Boundary.Program

/-!
# CppFormalization.Cpp4.Boundary.Transport.Program

Whole-program boundary transport surface.
-/

namespace Cpp4

/-- Transport for all internal-function boundaries packaged by a program boundary. -/
structure ProgramBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {P P' : Program}
    {hP : ProgramTyping P} (before : ProgramBoundary χ σ hP)
    (afterTyping : ProgramTyping P') : Type 1 where
  sourceBoundary : ProgramBoundary χ σ hP := before
  internalTransport :
    ∀ {f : FunctionName} {d : InternalFunctionDef}
      (hLookup : P'.lookupInternal f = some d),
      InternalFunctionBoundary χ' σ' (afterTyping.internalTyped hLookup)

namespace ProgramBoundaryTransport

/-- Apply whole-program boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {P P' : Program} {hP : ProgramTyping P} {hP' : ProgramTyping P'}
    {before : ProgramBoundary χ σ hP}
    (t : ProgramBoundaryTransport χ χ' σ σ' eff before hP') :
    ProgramBoundary χ' σ' hP' where
  internalBoundary := t.internalTransport

end ProgramBoundaryTransport

end Cpp4
