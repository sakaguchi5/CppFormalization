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
belongs to. -/
structure SafetyObligation (kind : Contracts.ObligationFamily) : Type where
  proposition : Prop
  evidence : Contracts.Requires proposition

namespace SafetyObligation

/-- Extract the evidence carried by a safety obligation. -/
def get {kind : Contracts.ObligationFamily} (h : SafetyObligation kind) : h.proposition :=
  h.evidence

end SafetyObligation

/-- A theorem-backed safety certificate.  This is still just explicit evidence;
the name only records that the evidence should come from lower facts rather than
from a programmer-facing obligation. -/
structure SafetyCertificate (kind : Contracts.CertifiedFamily) : Type where
  proposition : Prop
  evidence : Contracts.Certified proposition

namespace SafetyCertificate

/-- Extract the evidence carried by a safety certificate. -/
def get {kind : Contracts.CertifiedFamily} (h : SafetyCertificate kind) : h.proposition :=
  h.evidence

end SafetyCertificate

/-- Adopted policy marker for this layer. -/
def safetyFragmentPolicy : String :=
  "SafetyFragment names the intended safe C++ program range; it does not prove Boundary, Stability, or Soundness."

end SafetyFragment
end Cpp3
