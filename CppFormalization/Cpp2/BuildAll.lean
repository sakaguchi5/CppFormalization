import CppFormalization.Cpp2.All
import CppFormalization.Cpp2.AllV2
import CppFormalization.Cpp2.AllV3
import CppFormalization.Cpp2.Boundary.All
import CppFormalization.Cpp2.Core.All
import CppFormalization.Cpp2.Static.All
import CppFormalization.Cpp2.Typing.All
import CppFormalization.Cpp2.Semantics.All
import CppFormalization.Cpp2.Lemmas.All
import CppFormalization.Cpp2.Closure.All
import CppFormalization.Cpp2.Closure.Foundation.All
import CppFormalization.Cpp2.Closure.Internal.All
import CppFormalization.Cpp2.Closure.External.All
import CppFormalization.Cpp2.Closure.Transitions.All
import CppFormalization.Cpp2.Proof.All

/-!
# Cpp2.BuildAll

`lake build` で Cpp2 の全 Lean module を拾うための build 用 aggregate.

方針:
- canonical surface (`All`, `AllV2`, `AllV3`) はそのまま残す。
- build coverage のために、各 subdirectory の `All` をここからまとめて import する。
- `Frontier` は意図的に除外する。
-/
