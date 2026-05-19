import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureBoundaryDirectCoreSupportCI
import CppFormalization.Cpp2.Boundary.Structural.SeqStructuralBoundaryProjectionCI

namespace Cpp

/-!
# Closure.Internal.SeqTailRouteBoundaryFactoredCoreSupportCI

Factor the remaining `seq` direct-support debt.

After `SeqFunctionBodyClosureBoundaryDirectCoreSupportCI`, the only genuinely
large field is `tailRouteBoundary`: after an actual head-normal step, it must
choose the selected normal route and construct the tail boundary at that routed
post-environment.

This file splits that field into smaller units:

* route selection;
* tail boundary construction at a selected route;
* and, one layer lower, the structural/static/dynamic/adequacy components of
  that tail boundary.

C++ reading: after `s` falls through normally in `s; t`, the remaining obligation
is not another mysterious seq theorem.  It is exactly the obligation to enter
`t` at the post-state selected by the actual head-normal route.
-/

/--
Select the route used to enter the tail after an actual head-normal step.

This is still proof-architecture data: it records which `SeqHeadNormalRouteCI`
corresponds to the actual `BigStepStmt σ s .normal σ1`.
-/
structure SeqTailRouteSelectionCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  select :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      BigStepStmt σ s .normal σ1 →
      SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile

/--
Construct the tail boundary once a selected route is known.

This is the real boundary reconstruction obligation left by sequence closure.
-/
structure SeqTailBoundaryAtRouteCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  boundary :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyClosureBoundaryCI route.Θ σ1 t

/--
Direct sequence support with route selection separated from tail-boundary
construction.
-/
structure SeqFunctionBodyClosureBoundaryRoutedDirectCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  leftBoundary :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      BodyClosureBoundaryCI Γ σ (.seq s t) →
      BodyClosureBoundaryCI Γ σ s
  routeSelection : SeqTailRouteSelectionCoreSupportCI P
  tailBoundary : SeqTailBoundaryAtRouteCoreSupportCI P

/-- Forget routed-direct support to the previous direct-support shape. -/
def seqFunctionBodyClosureBoundaryDirectCoreSupportCI_of_routedDirect
    {P : StmtNormalPreservationCoreCI}
    (S : SeqFunctionBodyClosureBoundaryRoutedDirectCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryDirectCoreSupportCI P :=
  { leftBoundary := S.leftBoundary
    tailRouteBoundary := by
      intro Γ σ σ1 s t hentry hstepHead
      let route := S.routeSelection.select hentry hstepHead
      exact ⟨route, S.tailBoundary.boundary hentry hstepHead route⟩ }

/--
Boundary components for the tail at a selected route.

The structural component is theorem-backed from the whole sequence boundary, so
+this support only asks for the static/dynamic/adequacy components that depend on
+the selected route and post-state.
-/
structure SeqTailBoundaryComponentsAtRouteCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  static :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyStaticBoundaryCI route.Θ t

  dynamic :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyDynamicBoundary route.Θ σ1 t

  adequacy :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyAdequacyCI route.Θ σ1 t
        ((static hentry hstepHead route).profile)

/--
Assemble route-indexed tail boundaries from component support.

The shape/scopedness of the tail is inherited theoremically from the whole
sequence boundary; the route-sensitive static/dynamic/adequacy pieces are kept
explicit.
-/
def seqTailBoundaryAtRouteCoreSupportCI_of_components
    {P : StmtNormalPreservationCoreCI}
    (C : SeqTailBoundaryComponentsAtRouteCoreSupportCI P) :
    SeqTailBoundaryAtRouteCoreSupportCI P :=
  { boundary := by
      intro Γ σ σ1 s t hentry hstepHead route
      exact
        { structural := seq_tail_structural_boundary_of_entry (Θ := route.Θ) hentry
          static := C.static hentry hstepHead route
          dynamic := C.dynamic hentry hstepHead route
          adequacy := C.adequacy hentry hstepHead route } }

/--
Build routed-direct sequence support from separated route selection and
route-indexed boundary components.
-/
def seqFunctionBodyClosureBoundaryRoutedDirectCoreSupportCI_of_components
    {P : StmtNormalPreservationCoreCI}
    (leftBoundary :
      ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
        BodyClosureBoundaryCI Γ σ (.seq s t) →
        BodyClosureBoundaryCI Γ σ s)
    (R : SeqTailRouteSelectionCoreSupportCI P)
    (C : SeqTailBoundaryComponentsAtRouteCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryRoutedDirectCoreSupportCI P :=
  { leftBoundary := leftBoundary
    routeSelection := R
    tailBoundary := seqTailBoundaryAtRouteCoreSupportCI_of_components C }

/--
Compatibility wrapper: component-level routed support gives boundary-only seq
closure support.
-/
def seqFunctionBodyClosureBoundaryCoreSupportCI_of_routedComponents
    {P : StmtNormalPreservationCoreCI}
    (leftBoundary :
      ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
        BodyClosureBoundaryCI Γ σ (.seq s t) →
        BodyClosureBoundaryCI Γ σ s)
    (R : SeqTailRouteSelectionCoreSupportCI P)
    (C : SeqTailBoundaryComponentsAtRouteCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_direct
    (seqFunctionBodyClosureBoundaryDirectCoreSupportCI_of_routedDirect
      (seqFunctionBodyClosureBoundaryRoutedDirectCoreSupportCI_of_components
        leftBoundary R C))

end Cpp
