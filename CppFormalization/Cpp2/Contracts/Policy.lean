import CppFormalization.Cpp2.Contracts.Assumption
import CppFormalization.Cpp2.Contracts.Kind

namespace Cpp
namespace Contracts

/-!
# CppFormalization.Cpp2.Contracts.Policy

Policy for the contract layer.

The contract layer should define contract shapes and small wrappers.
It should not assert that a contract is globally available.

Allowed here:
- `structure`
- `inductive`
- `abbrev`
- `def`
- theorem-backed projections from already supplied evidence

Avoid here:
- `axiom`
- unconditional global providers for program obligations
- imports from `Closure.Internal` merely to discharge proof debt
-/

/-- Marker for the adopted policy: contracts are explicit assumptions. -/
def contractAssumptionPolicy : String :=
  "Contracts are explicit evidence passed to Proof/Closure, not unconditional axioms."

end Contracts
end Cpp
