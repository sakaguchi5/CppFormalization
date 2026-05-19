import CppFormalization.Cpp2.Closure.Internal.SeqTailRouteBoundaryFactoredCoreSupportCI
import CppFormalization.Cpp2.Static.Pure.SeqStructuralProjectionCI

namespace Cpp

/-!
# Closure.Internal.SeqNonAdequacyTheoremBackedAttemptCI

Attempt to theorem-back all non-adequacy pieces of the factored `seq` tail
route-boundary support.

Result of the split:

* The left boundary can be reconstructed theoremically up to the left adequacy
  field.
* Tail structural boundary is already theorem-backed from the whole sequence
  boundary.
* Tail dynamic boundary is theorem-backed once the selected route is aligned
  with the residual boundary produced by normal-preservation core.  This file
  exposes the route-free residual-boundary theorem and names the remaining
  alignment point instead of hiding it.
* Tail static boundary is route-sensitive.  It should be projected from the
  selected route/static payload.  It is not safe to fabricate it from arbitrary
  whole-sequence typing.

The only semantic residual we ultimately want to keep is adequacy.  However, in
this repo snapshot the selected route still packages static/adequacy together in
older surfaces, so a final “adequacy-only” implementation requires one more
route/static split.
-/

/--
The only non-theorem data needed to build the left boundary of `s` from a
sequence boundary is the left adequacy field.  Structural/static/dynamic are all
projected theoremically from the whole sequence boundary.
-/
structure SeqLeftAdequacyResidualCoreSupportCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  leftAdequacy :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      BodyAdequacyCI Γ σ s
        (seq_left_static_boundary_ci_of_entry hentry).profile

/--
The left closure boundary is theorem-backed except for the semantic adequacy
field, which is intentionally supplied as an adequacy residual.
-/
noncomputable def seq_left_boundary_of_adequacy_residual
    {P : StmtNormalPreservationCoreCI}
    (A : SeqLeftAdequacyResidualCoreSupportCI P)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyClosureBoundaryCI Γ σ s :=
  { structural := seq_left_structural_boundary_of_structural hentry.structural
    static := seq_left_static_boundary_ci_of_entry hentry
    dynamic := seq_left_dynamic_boundary_of_entry hentry
    adequacy := A.leftAdequacy hentry }

/--
Tail structural boundary is fully theorem-backed from the whole sequence
boundary and does not depend on adequacy, the route execution, or preservation.
-/
theorem seq_tail_structural_boundary_of_entry_at_route
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (_hstepHead : BigStepStmt σ s .normal σ1)
    (route : SeqHeadNormalRouteCI Γ σ s t σ1
      (seq_left_static_boundary_ci_of_entry hentry).profile) :
    BodyStructuralBoundary route.Θ t :=
  seq_tail_structural_boundary_of_entry (Θ := route.Θ) hentry

/--
A route-free theorem-backed tail dynamic witness.

This is the exact normal-preservation fact that `seq` needs after the head
falls through normally.  It produces the post environment selected by typing the
tail.  To turn this into `BodyDynamicBoundary route.Θ σ1 t`, the selected route
must be aligned with this residual boundary.  That alignment is the real
remaining route-selection/static issue, not a dynamic-safety issue.
-/
theorem seq_tail_dynamic_boundary_exists_of_normal_preservation_core
    (P : StmtNormalPreservationCoreCI)
    {Γ Δ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (htySeq : HasTypeStmtCI .normalK Γ (.seq s t) Δ)
    (hstate : ScopedTypedStateConcrete Γ σ)
    (hready : StmtReadyConcrete Γ σ (.seq s t))
    (hstepHead : BigStepStmt σ s .normal σ1) :
    ∃ Θ : TypeEnv, BodyDynamicBoundary Θ σ1 t := by
  rcases
      seq_left_normal_preserves_residual_boundary_of_normal_preservation_core
        P htySeq hstate hready hstepHead with
    ⟨Θ, _htyTail, hstateTail, hreadyTail⟩
  exact
    ⟨Θ,
      BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
        hstateTail hreadyTail⟩

/--
The remaining non-adequacy obstruction after the theorem-backed dynamic result:
the selected `SeqHeadNormalRouteCI` must use the same post-environment as the
residual boundary obtained from the actual head-normal step.

This is intentionally named as route alignment, not safety.  C++ meaning: the
route used to enter `t` after `s` falls through must be the actual post-env route
chosen by the typing/evaluation of `s; t`.
-/
structure SeqTailRouteDynamicAlignmentCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  dynamicAtRoute :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyDynamicBoundary route.Θ σ1 t

/--
Adequacy-only residual for the selected tail static boundary.

Once a route-specific static boundary has been selected theoremically, the only
remaining semantic field for the tail boundary should be this adequacy provider.
-/
structure SeqTailAdequacyResidualAtRouteCoreSupportCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  adequacy :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      (tailStatic : BodyStaticBoundaryCI route.Θ t) →
      BodyAdequacyCI route.Θ σ1 t tailStatic.profile

/--
A final component assembler once route selection, route static, and route dynamic
have been supplied.  This keeps adequacy as the only semantic residual.

The point of this wrapper is to make the next target precise: eliminate the
`routeStatic` and `routeDynamic` inputs by projecting them theoremically from the
selected route / residual boundary alignment.
-/
def seqTailBoundaryComponentsAtRouteCoreSupportCI_of_adequacyResidual
    {P : StmtNormalPreservationCoreCI}
    (routeStatic :
      ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
        (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
        (hstepHead : BigStepStmt σ s .normal σ1) →
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyStaticBoundaryCI route.Θ t)
    (routeDynamic : SeqTailRouteDynamicAlignmentCI P)
    (A : SeqTailAdequacyResidualAtRouteCoreSupportCI P) :
    SeqTailBoundaryComponentsAtRouteCoreSupportCI P :=
  { static := routeStatic
    dynamic := routeDynamic.dynamicAtRoute
    adequacy := by
      intro Γ σ σ1 s t hentry hstepHead route
      exact A.adequacy hentry hstepHead route
        (routeStatic hentry hstepHead route) }

/--
Direct support assembled with theorem-backed left boundary and theorem-backed
structural/dynamic shape, leaving adequacy explicit and route-static alignment
as the next concrete target.
-/
def seqFunctionBodyClosureBoundaryCoreSupportCI_of_nonAdequacyAttempt
    {P : StmtNormalPreservationCoreCI}
    (leftA : SeqLeftAdequacyResidualCoreSupportCI P)
    (R : SeqTailRouteSelectionCoreSupportCI P)
    (routeStatic :
      ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
        (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
        (hstepHead : BigStepStmt σ s .normal σ1) →
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyStaticBoundaryCI route.Θ t)
    (routeDynamic : SeqTailRouteDynamicAlignmentCI P)
    (tailA : SeqTailAdequacyResidualAtRouteCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_routedComponents
    (seq_left_boundary_of_adequacy_residual leftA)
    R
    (seqTailBoundaryComponentsAtRouteCoreSupportCI_of_adequacyResidual
      routeStatic routeDynamic tailA)

end Cpp
