import CppFormalization.Cpp3.Static.ControlProfile

/-!
# CppFormalization.Cpp3.Static.FunctionBodyControl

Static control surface for C++ function bodies.

A function body may complete normally or return.  An uncaught top-level
`break` or `continue` is not a successful function-body outcome, so the static
function-body boundary must rule out those escaping channels.
-/

namespace Cpp3
namespace Static

/-- Static control surface required of a C++ function body.

This is deliberately a static statement-control condition, not a runtime
provider.  C++ function bodies do not accept uncaught top-level `break` or
`continue`; those channels must be captured by an enclosing loop/switch-like
construct before reaching the function-body boundary. -/
structure FunctionBodyControlSurface (body : CppStmt) : Type where
  noEscapingBreak :
    ¬ StaticStmtControl body .breakK
  noEscapingContinue :
    ¬ StaticStmtControl body .continueK

namespace FunctionBodyControlSurface

/-- Project the no-escaping-break condition. -/
theorem noBreak
    {body : CppStmt}
    (h : FunctionBodyControlSurface body) :
    ¬ StaticStmtControl body .breakK :=
  h.noEscapingBreak

/-- Project the no-escaping-continue condition. -/
theorem noContinue
    {body : CppStmt}
    (h : FunctionBodyControlSurface body) :
    ¬ StaticStmtControl body .continueK :=
  h.noEscapingContinue

end FunctionBodyControlSurface

end Static
end Cpp3
