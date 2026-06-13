import CppFormalization.Cpp4.Static.FunctionShape

/-!
# CppFormalization.Cpp4.Static.ProgramShape

Static shape for whole Cpp4 programs.
-/

namespace Cpp4

/-- Whole-program static shape.  This layer checks declaration consistency and the
static shape of every internal definition known to the program. -/
structure ProgramStaticShape (P : Program) : Type where
  internalsDeclared : Program.InternalsDeclared P
  internalShape : ∀ {f d}, P.lookupInternal f = some d → InternalFunctionStaticShape d
  internalNameMatchesLookup : ∀ {f d}, P.lookupInternal f = some d → d.name = f

namespace ProgramStaticShape

/-- Extract static shape for a known internal definition. -/
def functionShape {P : Program} (hP : ProgramStaticShape P)
    {f : FunctionName} {d : InternalFunctionDef} (hLookup : P.lookupInternal f = some d) :
    InternalFunctionStaticShape d :=
  hP.internalShape hLookup

/-- Extract static body shape for a known internal definition. -/
def bodyShape {P : Program} (hP : ProgramStaticShape P)
    {f : FunctionName} {d : InternalFunctionDef} (hLookup : P.lookupInternal f = some d) :
    StaticBlockShape d.body :=
  (hP.functionShape hLookup).blockShape

end ProgramStaticShape

end Cpp4
