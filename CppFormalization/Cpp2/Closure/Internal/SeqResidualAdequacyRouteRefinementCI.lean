import CppFormalization.Cpp2.Closure.Internal.SeqTailCoarseTypingAtSelectedNormalCI

namespace Cpp

/-!
# Closure.Internal.SeqResidualAdequacyRouteRefinementCI

Small refinement layer for the current `seq` residuals.

This file advances the three current `seq` targets without changing the existing
public route:

1. turn selected-tail coarse typing into a theorem/projection-backed consequence
   of selected-tail static source coverage;
2. supply the left adequacy residual directly from the already reconstructed left
   boundary;
3. expose the tail adequacy residual as “adequacy projected from a recursive tail
   boundary whose static component is the selected route static component”.

C++ reading: for `s; t`, once the left statement has fallen through normally, the
remaining work is exactly to enter `t` at the selected post-environment and
post-state.  Static typing of `t` is a static route fact; left adequacy is the
local adequacy of `s`; tail adequacy is the semantic component of the recursive
tail boundary.
-/

/-!
## 1. Coarse selected-tail typing from selected-tail static source coverage
-/

/--
Aligned selected-tail static sources immediately give the coarse selected-tail
typing support.

This is the intended lower-static theorem shape: once the selected normal slot
has been aligned with `hp`, the static source for the tail at `hp.Θ` already
contains `typed0`.
-/
def seqTailCoarseTypingAtSelectedNormalCI_of_alignedStaticSources
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI) :
    SeqTailCoarseTypingAtSelectedNormalCI :=
  { tailTyped := by
      intro Γ σ s t hentry D N hp hsel
      exact ((S.sourceFromSelected hentry D N hp hsel).toStatic).typed0 }

/--
The same theorem/projection-backed path, presented at the older `typed0` support
surface used by the tail-return decision layer.
-/
def seqTailReturnTyped0SupportCI_of_alignedStaticSources
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI) :
    SeqTailReturnTyped0SupportCI :=
  seqTailReturnTyped0SupportCI_of_tailCoarseTyping
    (seqTailCoarseTypingAtSelectedNormalCI_of_alignedStaticSources S)

/--
If the source coverage is already canonical, we can still extract the coarse
selected-tail typing fact.  The queried `D`, `N`, and alignment proof are not
used, because canonical source coverage provides the tail static source for every
left-normal payload in the profile.
-/
noncomputable def seqTailCoarseTypingAtSelectedNormalCI_of_canonicalStaticSources
    (S : SeqCanonicalSelectedTailStaticSourceCoverageCI) :
    SeqTailCoarseTypingAtSelectedNormalCI :=
  { tailTyped := by
      intro Γ σ s t hentry D N hp _hsel
      exact ((S.source hentry hp).toStatic).typed0 }

/--
Canonical selected-tail static source coverage also discharges the older
tail-return `typed0` support.
-/
noncomputable def seqTailReturnTyped0SupportCI_of_canonicalStaticSources
    (S : SeqCanonicalSelectedTailStaticSourceCoverageCI) :
    SeqTailReturnTyped0SupportCI :=
  seqTailReturnTyped0SupportCI_of_tailCoarseTyping
    (seqTailCoarseTypingAtSelectedNormalCI_of_canonicalStaticSources S)

/--
Split return-decision coverage plus aligned selected-tail static sources gives
the lower selected-tail route typing object.

This keeps the current return-decision layer usable, but removes the temptation
to treat coarse `typed0` as a return-channel fact.
-/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_returnTypingAndAlignedStaticSources
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  seqSelectedTailStaticRouteTypingCI_of_returnTypingAndTailCoarseTyping
    (seqTailCoarseTypingAtSelectedNormalCI_of_alignedStaticSources S)
    C

/-!
## 2. Left adequacy directly from the existing left boundary
-/

/--
The left adequacy residual is not an independent `seq` obligation once the left
boundary can be reconstructed from the whole sequence boundary.

C++ reading: the profile of `s` used inside `s; t` is already the profile of the
left closure boundary, so its adequacy is just that boundary's adequacy field.
-/
noncomputable def seqLeftAdequacyResidualCoreSupportCI_of_leftEntryBoundary
    (P : StmtNormalPreservationCoreCI) :
    SeqLeftAdequacyResidualCoreSupportCI P :=
  { leftAdequacy := by
      intro Γ σ s t hentry
      exact (seq_left_closure_boundary_ci_of_entry hentry).adequacy }

/--
A convenience assembler for the static-route payload when only the direct left
adequacy path needs to be selected explicitly.
-/
noncomputable def seqSelectedHeadNormalRoutePayloadStaticRouteCI_of_directLeftAdequacy
    {P : StmtNormalPreservationCoreCI}
    (T : SeqSelectedTailStaticRouteTypingCI)
    (A : SeqSelectedTailAdequacyForStaticRouteTypingCI T P) :
    SeqSelectedHeadNormalRoutePayloadStaticRouteCI P :=
  { tailStatic := T
    leftAdequacy := seqLeftAdequacyResidualCoreSupportCI_of_leftEntryBoundary P
    tailAdequacy := A }

/-!
## 3. Tail adequacy as a semantic residual over the selected static route
-/

/--
A recursive/case-driver tail boundary whose static component is known to be the
static component selected by lower static route typing.

The boundary itself may come from a recursive closure/case-driver layer.  This
record states the exact alignment needed to project its adequacy into
`SeqSelectedTailAdequacyForStaticRouteTypingCI`.
-/
structure SeqSelectedTailBoundaryForStaticRouteTypingCI
    (T : SeqSelectedTailStaticRouteTypingCI)
    (_P : StmtNormalPreservationCoreCI) : Type where
  boundary :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyClosureBoundaryCI hp.Θ σ1 t

  static_eq :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      (boundary hentry hstepHead hp).static = T.static hentry hp

namespace SeqSelectedTailBoundaryForStaticRouteTypingCI

/--
Project selected-tail adequacy from a recursive tail boundary with aligned static
data.
-/
noncomputable def toTailAdequacy
    {T : SeqSelectedTailStaticRouteTypingCI}
    {P : StmtNormalPreservationCoreCI}
    (B : SeqSelectedTailBoundaryForStaticRouteTypingCI T P) :
    SeqSelectedTailAdequacyForStaticRouteTypingCI T P :=
  { adequacy := by
      intro Γ σ σ1 s t hentry hstepHead hp
      have hprofile :
          (B.boundary hentry hstepHead hp).static.profile =
            (T.static hentry hp).profile := by
        exact congrArg (fun st => st.profile)
          (B.static_eq hentry hstepHead hp)
      exact hprofile ▸ (B.boundary hentry hstepHead hp).adequacy }

end SeqSelectedTailBoundaryForStaticRouteTypingCI

/--
Assemble the current static-route payload from:

* lower selected-tail static route typing;
* direct left adequacy from the existing left boundary;
* a recursive tail boundary whose static component is aligned with the selected
  static route.
-/
noncomputable def seqSelectedHeadNormalRoutePayloadStaticRouteCI_of_tailBoundary
    {P : StmtNormalPreservationCoreCI}
    (T : SeqSelectedTailStaticRouteTypingCI)
    (B : SeqSelectedTailBoundaryForStaticRouteTypingCI T P) :
    SeqSelectedHeadNormalRoutePayloadStaticRouteCI P :=
  seqSelectedHeadNormalRoutePayloadStaticRouteCI_of_directLeftAdequacy
    T B.toTailAdequacy

/--
Route-projected version of the same idea.

This is closer to the boundary-level case-driver surface: after route selection,
the recursive side supplies a tail boundary at `route.Θ`; if its static boundary
is the route-projected static boundary, its adequacy is exactly the remaining
selected-route tail adequacy residual.
-/
structure SeqTailBoundaryForSelectedRouteCoreSupportCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  boundary :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyClosureBoundaryCI route.Θ σ1 t

  static_eq :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      (boundary hentry hstepHead route).static =
        seq_tail_static_boundary_ci_of_head_normal_route_projected
          hentry hstepHead route

namespace SeqTailBoundaryForSelectedRouteCoreSupportCI

/--
Project selected-route tail adequacy from a recursive route tail boundary with
aligned static data.
-/
noncomputable def toSelectedRouteAdequacy
    {P : StmtNormalPreservationCoreCI}
    (B : SeqTailBoundaryForSelectedRouteCoreSupportCI P) :
    SeqTailAdequacyForSelectedRouteCoreSupportCI P :=
  { adequacy := by
      intro Γ σ σ1 s t hentry hstepHead route
      have hprofile :
          (B.boundary hentry hstepHead route).static.profile =
            (seq_tail_static_boundary_ci_of_head_normal_route_projected
              hentry hstepHead route).profile := by
        exact congrArg (fun st => st.profile)
          (B.static_eq hentry hstepHead route)
      exact hprofile ▸ (B.boundary hentry hstepHead route).adequacy }

end SeqTailBoundaryForSelectedRouteCoreSupportCI

/--
Boundary-level sequence support with direct left adequacy and route-projected tail
adequacy.

The non-adequacy pieces remain theorem/projection-backed by
`seqFunctionBodyClosureBoundaryCoreSupportCI_of_routeTheoremBacked`; the supplied
recursive tail boundary is used only to extract the semantic adequacy field.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_directLeftAndRouteTailBoundary
    {P : StmtNormalPreservationCoreCI}
    (B : SeqTailBoundaryForSelectedRouteCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_routeTheoremBacked
    (seqLeftAdequacyResidualCoreSupportCI_of_leftEntryBoundary P)
    B.toSelectedRouteAdequacy

end Cpp
