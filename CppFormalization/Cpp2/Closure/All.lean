import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.Interface
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosure

/-!
# Cpp2.Closure.All

Canonical aggregate for the closure subsystem.

方針:
- default aggregate は mainline wrapper だけを公開面として集約する。
- legacy surface は `CppFormalization.Cpp2.Closure.Legacy.All` から明示的に読む。
- CI / compatibility / replay kernel などの implementation detail は
  必要な利用側が個別に import する。
-/
