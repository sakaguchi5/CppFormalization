import CppFormalization.Cpp2.Closure.Transitions.OpenCloseLowLevelTheorems
import CppFormalization.Cpp2.Closure.Transitions.Minor.OpenScopeDecomposition

namespace Cpp

/-!
# Closure.Transitions.Scope.OpenPreservation

Canonical public entry point for open-scope transition facts.

The current proofs still live in the historical files
`OpenCloseLowLevelTheorems` and `Minor.OpenScopeDecomposition`; this file is the
new scope-oriented facade.  Future refactors should move the actual open-scope
low-level helpers and preservation theorem here, while keeping the public import
path stable.
-/

end Cpp
