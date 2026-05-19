import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Boundary.Body.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Typing.ControlProfile
import CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary
import CppFormalization.Cpp2.Boundary.Adequacy.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Static.Safety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureResultCI
import CppFormalization.Cpp2.Closure.Internal.SeqBoundaryStaticDecompositionCI
import CppFormalization.Cpp2.Continuation.Route.Seq

namespace Cpp

/-!
# Seq scaffold and selected-route core

Extracted from `FunctionBodyCaseSplitCI.lean`.
This file owns the seq scaffold/static/slot/selected-route layer.
-/

/-!
## Seq scaffold extraction

The old `seq_left_closure_scaffold_ci_of_entry` and
`seq_tail_closure_scaffold_ci_of_left_normal` axioms hid several different
responsibilities in one package. The canonical sequence closure surfaces in
this file are now route-aware: the tail is entered through the selected
`SeqHeadNormalRouteCI`, not through an arbitrary bare normal typing witness.
The old explicit-tail-boundary surfaces have been removed from this file; callers should use the selected-route callback shape.

The scaffold pieces are built from narrower pieces:

* structural data is theorem-backed from the whole sequence boundary;
* left `typed0` is theorem-backed from the whole old typing payload;
* whole-sequence normal/return profile payloads are decomposed into explicit
  `Prop`-level seq provenance certificates;
* left profile selection and left root/coherence selection are separated;
* root/coherence is definitionally assembled from Type-level profile support;
* left adequacy remains a separate semantic obligation;
* tail static and tail adequacy are packaged together behind the actual
  left-normal route, because the tail environment is path-sensitive and must not
  be projected from the whole sequence return channel.
-/

structure SeqLeftClosureScaffoldCI
    (Γ : TypeEnv) (σ : State) (s : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ s
  static : BodyStaticBoundaryCI Γ s
  adequacy : BodyAdequacyCI Γ σ s static.profile

structure SeqTailClosureScaffoldCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  structural : BodyStructuralBoundary Θ t
  static : BodyStaticBoundaryCI Θ t
  adequacy : BodyAdequacyCI Θ σ1 t static.profile


/-!
Seq static decomposition / slot selection was extracted to
`CppFormalization.Cpp2.Static.Pure.SeqStaticDecompositionCI`.
-/

/-!
Seq selected route and tail adequacy payloads were extracted to
`CppFormalization.Cpp2.Continuation.Route.Seq`.
-/

end Cpp
