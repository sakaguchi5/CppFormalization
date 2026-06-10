import CppFormalization.Cpp3.Soundness2.Source.LocalControl

/-!
# CppFormalization.Cpp3.Soundness2.Derive.LocalControl

Local-control derivations from source theorem bundles.
-/

namespace Cpp3
namespace Soundness2
namespace Derive

/-- The local-control source bundle is already the theorem surface consumed by
Soundness2 final assembly.  This def fixes the derivation handoff point. -/
def localControlSourceTheorems
    (sources : Source.LocalControlSourceTheorems) :
    Source.LocalControlSourceTheorems :=
  sources

end Derive
end Soundness2
end Cpp3
