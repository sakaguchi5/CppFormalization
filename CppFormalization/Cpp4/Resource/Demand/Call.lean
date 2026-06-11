import CppFormalization.Cpp4.Core.Program
import CppFormalization.Cpp4.Resource.Demand.Expr

/-!
# CppFormalization.Cpp4.Resource.Demand.Call

Demand surfaces for function calls.
-/

namespace Cpp4

/-- Resource demand required to perform a call. -/
structure CallDemand where
  demands : DemandSet

namespace CallDemand

/-- Base call demand: the callee must resolve in the callable environment. -/
def callable (f : FunctionName) : CallDemand where
  demands := [.callable f]

/-- Build a call demand from a callee and already-computed argument demands. -/
def withArgs (f : FunctionName) (args : List ExprDemand) : CallDemand where
  demands := .callable f :: args.foldr (fun arg acc => arg.demands ++ acc) []

/-- External contract-only call demand surface. -/
def externalContractSurface (f : FunctionName) : CallDemand :=
  callable f

end CallDemand

end Cpp4
