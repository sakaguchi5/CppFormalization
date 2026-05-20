import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Continuation

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: stability package

This is the final route-local package for the clean-room seq-tail replay layer.
It deliberately contains no broad fallback axiom.  Runtime tail readiness is
obtained only by materializing `StmtReplay`.
-/

/--
Route-local seq-tail stability.

The package keeps the three mathematically distinct components visible:

* `postState`: preservation-shaped state/environment agreement after the left
  normal step;
* `replay`: C++-meaningful replay witness for the selected tail;
* `static`/`adequacy`: selected route payloads, exposed by projections below.
-/
structure StabilityAtRoute
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  postState : PostState route
  replay : StmtReplay route t

namespace StabilityAtRoute

/-- Forget stability to the smaller continuation package. -/
def toPackage
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : StabilityAtRoute route) :
    Package route :=
  { postState := h.postState
    replay := h.replay }

/-- Dynamic continuation boundary induced by route-local stability. -/
def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : StabilityAtRoute route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  h.toPackage.toDynamicBoundary

/-- Compatibility view as the existing body dynamic boundary. -/
def toBodyDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : StabilityAtRoute route) :
    BodyDynamicBoundary route.Θ σ1 t :=
  h.toPackage.toBodyDynamicBoundary

/-- Static boundary selected by the route. -/
def static
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (_h : StabilityAtRoute route) :
    BodyStaticBoundaryCI route.Θ t :=
  tailStatic route

/-- Semantic adequacy selected by the route. -/
noncomputable def adequacy
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (_h : StabilityAtRoute route) :
    BodyAdequacyCI route.Θ σ1 t (tailStatic route).profile :=
  tailAdequacy route

end StabilityAtRoute

end SeqTailReplay2
end Cpp
