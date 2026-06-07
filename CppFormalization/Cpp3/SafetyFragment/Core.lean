import CppFormalization.Cpp3.Contracts.Core.All
import CppFormalization.Cpp3.Effects.All

/-!
# CppFormalization.Cpp3.SafetyFragment.Core

Core vocabulary for the Cpp3 safety fragment.

`SafetyFragment` is not a proof of soundness.  It names the range of programs
for which later Boundary/Stability/Continuation/Soundness layers should be able
to rule out unclassified stuckness.

The important policy is the same as `Contracts/Core`: every safety fact is
explicit evidence.  This layer introduces no global axiom and no unconditional
provider.
-/

namespace Cpp3
namespace SafetyFragment

/-- A programmer-facing safety obligation, labeled by the contract family it
belongs to.

The proposition is an argument rather than a hidden field, so a package of this
form is visibly evidence for a particular obligation `P`. -/
structure SafetyObligation
    (kind : Contracts.ObligationFamily) (P : Prop) : Type where
  evidence : Contracts.Requires P

namespace SafetyObligation

/-- Extract the evidence carried by a safety obligation. -/
def get {kind : Contracts.ObligationFamily} {P : Prop}
    (h : SafetyObligation kind P) : P :=
  h.evidence

end SafetyObligation

/-- A theorem-backed safety certificate.  This is still just explicit evidence;
the name only records that the evidence should come from lower facts rather than
from a programmer-facing obligation.

The certified proposition is an argument rather than a hidden field, keeping the
meaning of the certificate visible at the type level. -/
structure SafetyCertificate
    (kind : Contracts.CertifiedFamily) (P : Prop) : Type where
  evidence : Contracts.Certified P

namespace SafetyCertificate

/-- Extract the evidence carried by a safety certificate. -/
def get {kind : Contracts.CertifiedFamily} {P : Prop}
    (h : SafetyCertificate kind P) : P :=
  h.evidence

end SafetyCertificate

/-- Adopted policy marker for this layer. -/
def safetyFragmentPolicy : String :=
  "SafetyFragment names the intended safe C++ program range; it does not prove Boundary, Stability, or Soundness."

end SafetyFragment
end Cpp3
