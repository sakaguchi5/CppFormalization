import CppFormalization.Cpp3.Soundness2.Source.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ScopeExit

Realized scope-exit theorem bundle for the closed-internal Soundness2 route.

This layer is separate from local control because C++ block execution has an
extra scope-close step after the opened block body has already been classified.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Realizer bundle for scope-exit source theorems. -/
structure ScopeExitRealizationTheorems : Type where
  blockClose : Source.BlockCloseSourceTheorem

namespace ScopeExitRealizationTheorems

/-- Convert realized scope-exit theorem pieces into the source bundle. -/
def toSourceTheorems
    (R : ScopeExitRealizationTheorems) :
    Source.ScopeExitSourceTheorems where
  blockClose := R.blockClose

end ScopeExitRealizationTheorems

end Realize
end Soundness2
end Cpp3
