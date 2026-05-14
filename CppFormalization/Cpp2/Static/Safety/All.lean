import CppFormalization.Cpp2.Static.Safety.Assumptions
import CppFormalization.Cpp2.Static.Safety.StateBoundary
import CppFormalization.Cpp2.Static.Safety.Readiness
import CppFormalization.Cpp2.Static.Safety.ReadinessInversions
import CppFormalization.Cpp2.Static.Safety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Static.Safety.ReadinessObjectDeclBridge
/-!
# CppFormalization.Cpp2.Static.Safety.All

Aggregate for static safety vocabulary.

`Static.Safety` may depend on Core, Typing, Semantics, runtime-state lemmas,
and `Static.Pure`-level facts.
It must not depend on Closure, adequacy, preservation, or boundary assembly.

Current split:
- `Assumptions`: coarse safety predicates and ideal boundary assumptions.
- `StateBoundary`: runtime/state-side safety boundary vocabulary.
- `Readiness`: concrete place/expression/statement readiness.
- `ReadinessInversions`: pure inversion lemmas for concrete readiness.
-/
