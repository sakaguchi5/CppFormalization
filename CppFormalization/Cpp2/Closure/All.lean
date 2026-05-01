import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyWitnessCI
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.Internal.SecondaryAssetsAllCI
import CppFormalization.Cpp2.Closure.Internal.Transport.All
import CppFormalization.Cpp2.Closure.External.Interface
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosure

/-!
# Cpp2.Closure.All

Canonical aggregate for the closure subsystem.

方針:
- default aggregate は mainline wrapper に加えて current internal transport aggregate も集約する。
- legacy surface は `CppFormalization.Cpp2.Closure.Legacy.All` から明示的に読む。
- Frontier は canonical aggregate には含めない。
-/
