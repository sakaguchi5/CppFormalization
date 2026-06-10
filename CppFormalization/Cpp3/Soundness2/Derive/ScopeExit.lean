import CppFormalization.Cpp3.Soundness2.Source.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness2.Derive.ScopeExit

Scope-exit derivations from source theorem bundles.
-/

namespace Cpp3
namespace Soundness2
namespace Derive

/-- The scope-exit source bundle is the theorem surface consumed by final assembly. -/
def scopeExitSourceTheorems
    (sources : Source.ScopeExitSourceTheorems) :
    Source.ScopeExitSourceTheorems :=
  sources

end Derive
end Soundness2
end Cpp3
