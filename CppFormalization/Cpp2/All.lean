import CppFormalization.Cpp2.Boundary.All
import CppFormalization.Cpp2.Core.All
import CppFormalization.Cpp2.Static.All
import CppFormalization.Cpp2.Typing.All
import CppFormalization.Cpp2.Semantics.All
import CppFormalization.Cpp2.Lemmas.All
import CppFormalization.Cpp2.Closure.All
import CppFormalization.Cpp2.Proof.All
import CppFormalization.Cpp2.Frontier.All

/-!
# Cpp2.All

Single Cpp2-wide build-coverage aggregate.

Policy:
- every Cpp2 directory with an `All.lean` aggregate is imported here;
- `BuildAll.lean` should import this file only;
- Frontier is included for coverage, not as the canonical proof surface.
-/
