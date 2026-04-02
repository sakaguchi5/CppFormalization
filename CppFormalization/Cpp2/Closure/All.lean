import CppFormalization.Cpp2.Closure.Foundation.StateBoundary
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureCI
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.Interface
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosure

/-!
# Cpp2.Closure.All

Canonical aggregate for the closure subsystem after the Stage 7 mainline switch.

方針:
- default aggregate は mainline wrapper (`InternalClosureRoadmap`, `Interface`,
  `ReflectiveStdClosure`) を公開面として採用する。
- V2 implementation detail modules (`*CI`) は、必要な基礎 internal files 以外は
  ここからは直接 re-export しない。
- legacy surface は `Closure.Legacy.All` から明示的に読む。
-/
