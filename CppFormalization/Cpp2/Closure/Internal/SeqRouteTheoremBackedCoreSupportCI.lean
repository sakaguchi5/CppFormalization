import CppFormalization.Cpp2.Closure.Internal.SeqNonAdequacyTheoremBackedAttemptCI

namespace Cpp

/-!
# Closure.Internal.SeqRouteTheoremBackedCoreSupportCI

Route-aware theorem-backed projections for the remaining non-adequacy pieces of
sequence tail reconstruction.

The actual `FunctionBodyCaseSplitCI` route object is stronger than a bare normal
witness:

* `SeqHeadNormalRouteCI` stores the selected post-environment `Θ`;
* it stores the selected left-normal typing witness `hleft`;
* it stores the actual head-normal step `hstepLeft`;
* and it stores the route-indexed tail static/adequacy payload.

Therefore route selection, tail static projection, and tail dynamic construction
can all be exposed as theorem-backed/projection-backed layers.  The semantic
adequacy debt can still be kept explicit by using
`SeqTailAdequacyForSelectedRouteCoreSupportCI`; the compatibility constructors at
bottom show how the existing route payload can also discharge it.
-/

/--
The selected route after a head-normal execution is already provided by the
route-aware sequence layer.

`P` is only the index of the surrounding core-support object.  Route selection
itself is static/semantic route data and does not consume the preservation core.
-/
noncomputable def seqTailRouteSelectionCoreSupportCI_of_entry
    (P : StmtNormalPreservationCoreCI) :
    SeqTailRouteSelectionCoreSupportCI P :=
  { select := by
      intro Γ σ σ1 s t hentry hstepHead
      exact seq_left_normalRoute_of_entry hentry hstepHead }

/--
Tail static boundary is a projection from the selected head-normal route.

This is the route-sensitive version: the tail boundary lives at `route.Θ`, not
at an arbitrary environment supplied by a caller.
-/
noncomputable def seq_tail_static_boundary_ci_of_head_normal_route_projected
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {Pleft : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (_hstepHead : BigStepStmt σ s .normal σ1)
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 Pleft) :
    BodyStaticBoundaryCI route.Θ t :=
  route.tail.static

/--
Tail dynamic boundary at the selected route environment, using only the pure
normal-preservation core.

This is the main replacement for the older path that used
`WhileReentryReadyProvider` directly.  C++ reading: after `s` falls through
normally in `s; t`, the state is typed at the selected post-environment and the
right-hand statement is ready there.
-/
def seqTailRouteDynamicAlignmentCI_of_normalPreservationCore
    (P : StmtNormalPreservationCoreCI) :
    SeqTailRouteDynamicAlignmentCI P :=
  { dynamicAtRoute := by
      intro Γ σ σ1 s t hentry _hstepHead route
      have hreadyLeft : StmtReadyConcrete Γ σ s :=
        seq_ready_left hentry.dynamic.safe
      have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
        P.preserve route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
      have hreadyRight : StmtReadyConcrete route.Θ σ1 t :=
        seq_ready_right_after_left_normal
          route.hleft hσ1 hentry.dynamic.safe route.hstepLeft
      exact
        BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
          hσ1 hreadyRight }

/--
Adequacy residual for the selected route static boundary.

This is narrower than the earlier residual that accepted an arbitrary
`tailStatic`: the static boundary is now fixed theoremically/projectionally as
`route.tail.static`.
-/
structure SeqTailAdequacyForSelectedRouteCoreSupportCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  adequacy :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (hstepHead : BigStepStmt σ s .normal σ1)
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      BodyAdequacyCI route.Θ σ1 t
        ((seq_tail_static_boundary_ci_of_head_normal_route_projected
          hentry hstepHead route).profile)

/--
Component support where route selection, route static, and route dynamic are all
provided by existing theorem/projection layers.  Only the selected-route tail
adequacy is left explicit.
-/
noncomputable def seqTailBoundaryComponentsAtRouteCoreSupportCI_of_routeTheoremBacked
    {P : StmtNormalPreservationCoreCI}
    (A : SeqTailAdequacyForSelectedRouteCoreSupportCI P) :
    SeqTailBoundaryComponentsAtRouteCoreSupportCI P :=
  { static := by
      intro Γ σ σ1 s t hentry hstepHead route
      exact seq_tail_static_boundary_ci_of_head_normal_route_projected
        hentry hstepHead route
    dynamic := (seqTailRouteDynamicAlignmentCI_of_normalPreservationCore P).dynamicAtRoute
    adequacy := by
      intro Γ σ σ1 s t hentry hstepHead route
      exact A.adequacy hentry hstepHead route }

/--
Boundary-level sequence closure support from theorem-backed non-adequacy pieces,
leaving only left adequacy and selected-route tail adequacy explicit.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_routeTheoremBacked
    {P : StmtNormalPreservationCoreCI}
    (leftA : SeqLeftAdequacyResidualCoreSupportCI P)
    (tailA : SeqTailAdequacyForSelectedRouteCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_routedComponents
    (seq_left_boundary_of_adequacy_residual leftA)
    (seqTailRouteSelectionCoreSupportCI_of_entry P)
    (seqTailBoundaryComponentsAtRouteCoreSupportCI_of_routeTheoremBacked tailA)

/--
Compatibility: the existing selected route already carries the tail adequacy
payload.  This discharges the selected-route adequacy residual by projection.

This is useful for current repo compatibility.  Conceptually, the remaining
semantic debt is now concentrated in the construction of the route payload
itself, not in tail boundary reconstruction.
-/
noncomputable def seqTailAdequacyForSelectedRouteCoreSupportCI_of_routePayload
    (P : StmtNormalPreservationCoreCI) :
    SeqTailAdequacyForSelectedRouteCoreSupportCI P :=
  { adequacy := by
      intro Γ σ σ1 s t hentry hstepHead route
      exact route.tail.support.toBodyAdequacyCI }

/--
Compatibility constructor using the existing left and route payloads.

This is the fully closed boundary-level seq support at the new core surface.  It
uses the pure preservation core for dynamic reconstruction and the existing
route payloads for static/adequacy.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_existingRoutePayload
    (P : StmtNormalPreservationCoreCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_routedComponents
    (fun hentry => seq_left_closure_boundary_ci_of_entry hentry)
    (seqTailRouteSelectionCoreSupportCI_of_entry P)
    (seqTailBoundaryComponentsAtRouteCoreSupportCI_of_routeTheoremBacked
      (seqTailAdequacyForSelectedRouteCoreSupportCI_of_routePayload P))

end Cpp
