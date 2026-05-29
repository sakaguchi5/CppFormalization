import CppFormalization.Cpp2.Closure.Function.FunctionBody
import CppFormalization.Cpp2.Legacy.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Package.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.StructuralAdmission.BodyStructuralBoundary
import CppFormalization.Cpp2.Profile.ControlProfile
import CppFormalization.Cpp2.Entry.StaticSafety.BodyDynamicBoundary
import CppFormalization.Cpp2.Adequacy.Body.BodyAdequacyCI
import CppFormalization.Cpp2.Route.Closure.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Preservation.Closure.SequentialNormalPreservation
import CppFormalization.Cpp2.Preservation.Closure.StmtControlPreservation
import CppFormalization.Cpp2.Entry.StaticSafety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Operational.Divergence
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureResultCI
import CppFormalization.Cpp2.Route.Closure.SeqClosureRouteCI
import CppFormalization.Cpp2.Route.Closure.IteClosureRouteCI

namespace Cpp


/-!
## Seq decomposition extracted

The seq scaffold/route/stability/closure shell previously accumulated
in this file now lives in:
* `SeqScaffoldRouteCI`
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
