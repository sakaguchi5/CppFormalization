import CppFormalization.Cpp4.Boundary.Function
import CppFormalization.Cpp4.Typing.Judgment.Surface.Program

/-!
# CppFormalization.Cpp4.Boundary.Program

Whole-program boundary surface.
-/

namespace Cpp4

/-- A program boundary packages boundaries for all internal definitions known by the
program typing certificate, at a supplied function-entry state.  Later function
entry setup can refine the state parameter per callable. -/
structure ProgramBoundary
    (χ : DemandContext) (σ : State) {P : Program} (hP : ProgramTyping P) : Type 1 where
  internalBoundary :
    ∀ {f : FunctionName} {d : InternalFunctionDef}
      (hLookup : P.lookupInternal f = some d),
      InternalFunctionBoundary χ σ (hP.internalTyped hLookup)

namespace ProgramBoundary

/-- Extract the function-body boundary for a known internal definition. -/
def bodyBoundary {χ : DemandContext} {σ : State} {P : Program} {hP : ProgramTyping P}
    (b : ProgramBoundary χ σ hP)
    {f : FunctionName} {d : InternalFunctionDef} (hLookup : P.lookupInternal f = some d) :
    FunctionBodyBoundary χ σ (ProgramTyping.bodyTyping hP hLookup) :=
  (b.internalBoundary hLookup).bodyBoundary

end ProgramBoundary

end Cpp4
