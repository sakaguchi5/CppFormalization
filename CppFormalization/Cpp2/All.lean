import CppFormalization.Cpp2.Core.All
import CppFormalization.Cpp2.Typing.All
import CppFormalization.Cpp2.Semantics.All
import CppFormalization.Cpp2.Static.All
import CppFormalization.Cpp2.Effects.All
import CppFormalization.Cpp2.Contracts.All
import CppFormalization.Cpp2.Boundary.All
import CppFormalization.Cpp2.Continuation.All
import CppFormalization.Cpp2.Proof.All
import CppFormalization.Cpp2.Closure.All
import CppFormalization.Cpp2.Roadmap.All
import CppFormalization.Cpp2.Frontier.All

/-!
# CppFormalization.Cpp2.All

Exhaustive aggregate for this directory.

This file imports every Lean file directly under this directory, except itself,
and every immediate child directory through that child directory's `All.lean`.

The order is dependency-oriented:

* `Core` is the substrate, with `Core.Types` as the bottom vocabulary.
* `Typing` and `Semantics` sit above `Core`.
* `Static`, `Effects`, `Contracts`, `Boundary`, `Continuation`, and `Proof`
  add increasingly rich theorem-facing structure.
* `Closure` is the high-level assembly layer.
* `Roadmap` / `Frontier` are intentionally last.
-/
