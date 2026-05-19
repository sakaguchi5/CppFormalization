import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Typing.ControlProfile
import CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Static.Safety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureResultCI
import CppFormalization.Cpp2.Closure.Internal.SeqClosureRouteCI
import CppFormalization.Cpp2.Closure.Internal.IteClosureRouteCI

namespace Cpp


/-!
## Seq decomposition extracted

The seq scaffold/route/stability/closure shell previously accumulated
in this file now lives in:
* `SeqScaffoldRouteCI`
* `SeqTailStabilityRouteCI`
* `SeqClosureRouteCI`
-/

/-!
## Ite decomposition extracted

The ite branch-boundary/profile/adequacy/closure route previously accumulated
in this file now lives in:
* `IteClosureRouteCI`

This file is now only a compatibility import surface for the compound-statement
case-split family.
-/

end Cpp
