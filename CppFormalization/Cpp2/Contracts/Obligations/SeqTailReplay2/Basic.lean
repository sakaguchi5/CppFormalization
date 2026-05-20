import CppFormalization.Cpp2.Continuation.Route.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Dynamic

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: route-local replay kernel

Clean-room reconstruction of the seq-tail replay idea.

Design points:

* The subject is an actual selected `SeqHeadNormalRouteCI`.
* We do not import the existing `SeqTailReplay` implementation.
* Post-state preservation is separated from replay/readiness materialization.
* Replay witnesses are path-sensitive C++ obligations, not global readiness
  transport principles.
-/

/--
Post-state preservation component for a selected seq head-normal route.

This is preservation-shaped: after the selected left-normal step, the route's
post-environment `route.Θ` and actual post-state `σ1` still agree concretely.
It should be supplied by normal-preservation theorems, not by replay witnesses.
-/
structure PostState
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  state : ScopedTypedStateConcrete route.Θ σ1

/--
Static tail boundary selected by the route.

This is just a named projection.  It keeps the clean-room API focused on the
selected route rather than on legacy seq-tail transport objects.
-/
def tailStatic
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    BodyStaticBoundaryCI route.Θ t :=
  route.tail.static

/--
Tail adequacy selected by the route.

This is semantic and path-sensitive: it is indexed by the actual post-state
reached by the selected left-normal execution.
-/
noncomputable def tailAdequacy
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    BodyAdequacyCI route.Θ σ1 t (tailStatic route).profile :=
  route.tail.support.toBodyAdequacyCI

end SeqTailReplay2
end Cpp
