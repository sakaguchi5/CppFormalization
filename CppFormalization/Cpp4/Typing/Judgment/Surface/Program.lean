import CppFormalization.Cpp4.Typing.Judgment.Surface.Function

/-!
# CppFormalization.Cpp4.Typing.Judgment.Surface.Program

Surface whole-program typing certificates.
-/

namespace Cpp4

/-- Whole-program surface typing.  Internal definitions must be declared in the
callable environment, and every internal definition must have a typed body. -/
structure ProgramTyping (P : Program) : Type 1 where
  internalsDeclared : Program.InternalsDeclared P
  internalTyped : ∀ {f d}, P.lookupInternal f = some d → InternalFunctionTyping d

namespace ProgramTyping

/-- Extract the typed body for a known internal definition. -/
def bodyTyping {P : Program} (hP : ProgramTyping P)
    {f : FunctionName} {d : InternalFunctionDef} (hLookup : P.lookupInternal f = some d) :
    FunctionBodyTyping d.sig d.body :=
  (hP.internalTyped hLookup).bodyTyping

end ProgramTyping

end Cpp4
