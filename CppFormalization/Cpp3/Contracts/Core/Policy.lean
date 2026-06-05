import CppFormalization.Cpp3.Contracts.Core.Assumption
import CppFormalization.Cpp3.Contracts.Core.Kind

namespace Cpp3
namespace Contracts

/-!
# CppFormalization.Cpp3.Contracts.Core.Policy

Policy for the Cpp3 contract layer.

`Contracts/Core` provides only the vocabulary for explicit evidence.  It should
not assert that any program obligation is globally available.

Allowed here:
* `structure`
* `inductive`
* `abbrev`
* `def`
* theorem-backed projections from already supplied evidence

Avoid here:
* `axiom`
* unconditional global providers for program obligations
* imports from proof/closure layers merely to discharge proof debt
-/

/-- Marker for the adopted policy. -/
def contractAssumptionPolicy : String :=
  "Contracts are explicit evidence passed to Cpp3 components, not unconditional axioms."

/-- Marker for the programmer-facing role of `Contracts/Program`. -/
def programmerFacingContractPolicy : String :=
  "Program contracts explain why a C++ effect is safe to continue from."

end Contracts
end Cpp3
