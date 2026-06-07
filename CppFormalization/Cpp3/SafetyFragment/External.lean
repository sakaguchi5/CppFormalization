import CppFormalization.Cpp3.SafetyFragment.Core

/-!
# CppFormalization.Cpp3.SafetyFragment.External

Safety-fragment hooks for external or not-yet-internalized C++ behavior.

The current Cpp3 core has no explicit external-call syntax.  This file therefore
only provides a small hook: when such behavior is later added, the safe fragment
can require an explicit external specification instead of silently treating the
behavior as globally safe.
-/

namespace Cpp3
namespace SafetyFragment

/-- A named external behavior stays inside the safe C++ fragment. -/
structure ExternalBehaviorSafetyFragment (tag : String) : Type where
  kind : Contracts.ContractKind :=
    .obligation .externalCallSpec
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace ExternalBehaviorSafetyFragment

def get {tag : String} (h : ExternalBehaviorSafetyFragment tag) : h.obligation :=
  h.evidence

end ExternalBehaviorSafetyFragment

/-- The external behavior respects its declared footprint. -/
structure ExternalFootprintRespected (tag : String) (fp : Effects.Footprint) : Type where
  kind : Contracts.ContractKind :=
    .obligation .externalCallFootprintRespected
  obligation : Prop
  evidence : Contracts.Requires obligation

/-- The external behavior respects its lifetime contract. -/
structure ExternalLifetimeRespected (tag : String) (fp : Effects.Footprint) : Type where
  kind : Contracts.ContractKind :=
    .obligation .externalCallLifetimeRespected
  obligation : Prop
  evidence : Contracts.Requires obligation

end SafetyFragment
end Cpp3
