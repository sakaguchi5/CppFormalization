import CppFormalization.Cpp2.Continuation.Route.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Boundary.Body.BodyClosureBoundaryCI

namespace Cpp

/-!
# Seq tail replay / stability obligations

Extracted aggressively from `Closure.Internal.SeqTailStabilityRouteCI`.
This module contains route-local tail replay and stability contracts.  These are
not closure shells: they are the conditions saying why the selected route can
enter the tail in the post-state.

Several components are still coarse placeholders.  The point of this move is to
make them visible as contract obligations, not as hidden closure internals.
-/

/--
Post-state component of the tail stability contract.

This is preservation-shaped: after the selected left-normal route, the route's
post-environment `route.Θ` and actual post-state `σ1` still agree concretely.
Long term, this component should be theorem-backed by normal preservation rather
than treated as a program contract.
-/
structure SeqTailPostStateAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  postState : ScopedTypedStateConcrete route.Θ σ1

/--
Name/scope/static component of the tail stability contract.

This is intentionally separated from runtime readiness.  The selected route
already determines `route.Θ`, and the tail static package lives exactly at that
environment.  This records the future split point for name-resolution and scope
stability.
-/
structure SeqTailNameScopeStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  typed0 : WellTypedFrom route.Θ t

/- =========================================================
   Constructor-aligned runtime replay skeleton
   ========================================================= -/

/--
Statement-constructor replay slots for the selected tail route.

This is intentionally still a lightweight contract skeleton: each field is a
slot corresponding to a `StmtReadyConcrete` constructor.  Later materialization
theorems can replace the `True` payloads by the exact constructor inputs
(`HasValueType`, `ExprReadyConcrete`, `PlaceReadyConcrete`, branch readiness,
and so on) without changing the route-level API.
-/
structure SeqTailStmtConstructorReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  skip :
    t = .skip → True
  exprStmt :
    ∀ {e : ValExpr}, t = .exprStmt e → True
  assign :
    ∀ {p : PlaceExpr} {e : ValExpr}, t = .assign p e → True
  declareObjNone :
    ∀ {τ : CppType} {x : Ident}, t = .declareObj τ x none → True
  declareObjSome :
    ∀ {τ : CppType} {x : Ident} {e : ValExpr},
      t = .declareObj τ x (some e) → True
  declareRef :
    ∀ {τ : CppType} {x : Ident} {p : PlaceExpr},
      t = .declareRef τ x p → True
  seq :
    ∀ {u v : CppStmt}, t = .seq u v → True
  ite :
    ∀ {c : ValExpr} {u v : CppStmt}, t = .ite c u v → True
  whileStmt :
    ∀ {c : ValExpr} {body : CppStmt}, t = .whileStmt c body → True
  block :
    ∀ {ss : StmtBlock}, t = .block ss → True
  breakStmt :
    t = .breakStmt → True
  continueStmt :
    t = .continueStmt → True
  returnNone :
    t = .returnStmt none → True
  returnSome :
    ∀ {e : ValExpr}, t = .returnStmt (some e) → True

namespace SeqTailStmtConstructorReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths that already have tail-ready. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailStmtConstructorReplayAtRouteCI route :=
  { skip := by intro _; trivial
    exprStmt := by intro e _; trivial
    assign := by intro p e _; trivial
    declareObjNone := by intro τ x _; trivial
    declareObjSome := by intro τ x e _; trivial
    declareRef := by intro τ x p _; trivial
    seq := by intro u v _; trivial
    ite := by intro c u v _; trivial
    whileStmt := by intro c body _; trivial
    block := by intro ss _; trivial
    breakStmt := by intro _; trivial
    continueStmt := by intro _; trivial
    returnNone := by intro _; trivial
    returnSome := by intro e _; trivial }

end SeqTailStmtConstructorReplayAtRouteCI

/-- Placeholder for replaying an ordinary value expression used by the selected tail. -/
def SeqTailValueUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_e : ValExpr) (_τ : CppType) : Prop :=
  True

/-- Placeholder for replaying an ordinary place used by the selected tail. -/
def SeqTailPlaceUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_p : PlaceExpr) (_τ : CppType) : Prop :=
  True

/--
Ordinary read replay slots for tail expressions and places.

The fields are already shaped for later materialization into
`ExprReadyConcrete` / `PlaceReadyConcrete`; the placeholder predicates can be
strengthened without changing this route-level interface.
-/
structure SeqTailOrdinaryReadReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  valueUse :
    ∀ {e : ValExpr} {τ : CppType},
      SeqTailValueUseReplayAtRouteCI route e τ
  placeUse :
    ∀ {p : PlaceExpr} {τ : CppType},
      SeqTailPlaceUseReplayAtRouteCI route p τ

namespace SeqTailOrdinaryReadReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailOrdinaryReadReplayAtRouteCI route :=
  { valueUse := by
      intro e τ
      trivial
    placeUse := by
      intro p τ
      trivial }

end SeqTailOrdinaryReadReplayAtRouteCI

/--
Placeholder for replaying a pointer expression used by a tail dereference after
the selected route.

Future refinement target:
replace `True` by the data needed for `PlaceReadyConcrete.deref`, namely

* the pointer expression has pointer type;
* it evaluates in the post-state to an address;
* the addressed cell is live and typed.
-/
def SeqTailDerefUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_e : ValExpr) (_τ : CppType) : Prop :=
  True

/--
Pointer-dereference replay slots.

This is shaped for the `PlaceReadyConcrete.deref` constructor.  The field is
still coarse, but `e` and `τ` are now part of a named predicate, so later we can
strengthen the predicate without changing the route-level API.
-/
structure SeqTailDerefPointerReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  derefUse :
    ∀ {e : ValExpr} {τ : CppType},
      SeqTailDerefUseReplayAtRouteCI route e τ

namespace SeqTailDerefPointerReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailDerefPointerReplayAtRouteCI route :=
  { derefUse := by
      intro e τ
      trivial }

end SeqTailDerefPointerReplayAtRouteCI

/--
Placeholder for replaying a loaded place after the selected route.

Future refinement target:
replace `True` by the data needed for `ExprReadyConcrete.load`, namely

* the place is ready in the post-state;
* it evaluates to an address;
* the addressed cell is readable and typed.
-/
def SeqTailLoadUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_p : PlaceExpr) (_τ : CppType) : Prop :=
  True

/--
Load-readability replay slots.

This is shaped for the `ExprReadyConcrete.load` constructor.  The field is still
coarse, but `p` and `τ` are now part of a named predicate, so later we can
strengthen the predicate without changing the route-level API.
-/
structure SeqTailLoadReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  loadUse :
    ∀ {p : PlaceExpr} {τ : CppType},
      SeqTailLoadUseReplayAtRouteCI route p τ

namespace SeqTailLoadReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailLoadReplayAtRouteCI route :=
  { loadUse := by
      intro p τ
      trivial }

end SeqTailLoadReplayAtRouteCI

/--
Read-set non-clobbering component for the selected tail route.

Compared with the old `witness : True` placeholder, this component now records
two constructor-oriented slots:

* `stmtShape` follows the constructors of `StmtReadyConcrete`;
* `ordinaryReads` is the future hook for ordinary expression/place replay.

The C++-dangerous deref/load cases stay in their own components below.
-/
structure SeqTailReadSetNonClobberAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  stmtShape : SeqTailStmtConstructorReplayAtRouteCI route
  ordinaryReads : SeqTailOrdinaryReadReplayAtRouteCI route

namespace SeqTailReadSetNonClobberAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailReadSetNonClobberAtRouteCI route :=
  { stmtShape := SeqTailStmtConstructorReplayAtRouteCI.trivial
    ordinaryReads := SeqTailOrdinaryReadReplayAtRouteCI.trivial }

end SeqTailReadSetNonClobberAtRouteCI

/--
Pointer/deref stability component for the selected tail route.

This is now a named wrapper around the future dereference replay slots, rather
than a bare placeholder.
-/
structure SeqTailPointerDerefStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  derefPointer : SeqTailDerefPointerReplayAtRouteCI route

namespace SeqTailPointerDerefStabilityAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailPointerDerefStabilityAtRouteCI route :=
  { derefPointer := SeqTailDerefPointerReplayAtRouteCI.trivial }

end SeqTailPointerDerefStabilityAtRouteCI

/--
Load readability preservation component for the selected tail route.

This is now a named wrapper around the future load-readability replay slots,
rather than a bare placeholder.
-/
structure SeqTailLoadReadabilityPreservationAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  loadReadability : SeqTailLoadReplayAtRouteCI route

namespace SeqTailLoadReadabilityPreservationAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailLoadReadabilityPreservationAtRouteCI route :=
  { loadReadability := SeqTailLoadReplayAtRouteCI.trivial }

end SeqTailLoadReadabilityPreservationAtRouteCI

/--
Runtime replay component of the tail stability contract.

The three named subcomponents are the C++-meaningful future split points.  At
this stage, `tailReady` is still the coarse runtime fact, but it is no longer
mixed with post-state preservation or tail static/profile adequacy.
-/
structure SeqTailRuntimeReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  readSet : SeqTailReadSetNonClobberAtRouteCI route
  derefPointer : SeqTailPointerDerefStabilityAtRouteCI route
  loadReadability : SeqTailLoadReadabilityPreservationAtRouteCI route
  tailReady : StmtReadyConcrete route.Θ σ1 t

namespace SeqTailRuntimeReplayAtRouteCI

/-- Compatibility constructor from the still-coarse tail readiness fact. -/
def ofTailReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (hready : StmtReadyConcrete route.Θ σ1 t) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
    derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
    loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial
    tailReady := hready }

end SeqTailRuntimeReplayAtRouteCI

/--
Route-local stability contract for the tail of `s; t`.


/--
Runtime replay components for the selected tail route.

This is the next refinement below `SeqTailRuntimeReplayAtRouteCI`: the C++
meaningful parts are named separately, and the remaining coarse step is only the
materialization theorem/obligation that turns those components into ordinary
`StmtReadyConcrete`.
-/
-/
structure SeqTailRuntimeReplayComponentsAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  readSet : SeqTailReadSetNonClobberAtRouteCI route
  derefPointer : SeqTailPointerDerefStabilityAtRouteCI route
  loadReadability : SeqTailLoadReadabilityPreservationAtRouteCI route

/- =========================================================
   Stage 3a: theorem-backed materialization for control-only tails
   ========================================================= -/

/--
Control-only tail shapes whose readiness is constructor-backed.

These cases do not need expression, place, load, dereference, alias, or
readability evidence.  Once the selected route says the tail is one of these
forms, `StmtReadyConcrete route.Θ σ1 t` follows directly by the corresponding
constructor.
-/
inductive SeqTailControlOnlyConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | skip :
      t = .skip →
      SeqTailControlOnlyConstructorAtRouteCI route
  | breakStmt :
      t = .breakStmt →
      SeqTailControlOnlyConstructorAtRouteCI route
  | continueStmt :
      t = .continueStmt →
      SeqTailControlOnlyConstructorAtRouteCI route
  | returnNone :
      t = .returnStmt none →
      SeqTailControlOnlyConstructorAtRouteCI route

/--
Materialize tail readiness for the control-only fragment.

This is the first theorem-backed replacement fragment for the coarse
`seq_tail_ready_of_runtime_replay_components_at_route_ci` obligation.
The runtime components are kept in the statement so callers can use this theorem
as a drop-in fragment of the component-based materialization route, but these
control-only constructors do not need them.
-/
theorem seq_tail_ready_of_runtime_replay_components_control_only_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hcontrol : SeqTailControlOnlyConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hcontrol with
  | skip h =>
      cases h
      exact StmtReadyConcrete.skip
  | breakStmt h =>
      cases h
      exact StmtReadyConcrete.breakStmt
  | continueStmt h =>
      cases h
      exact StmtReadyConcrete.continueStmt
  | returnNone h =>
      cases h
      exact StmtReadyConcrete.returnNone

/--
Assemble the runtime replay package for a control-only tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_control_only_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hcontrol : SeqTailControlOnlyConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_control_only_at_route_ci
        hentry route components hcontrol }

/--
Convenience constructor for the control-only fragment using the current coarse
component witnesses.

This is useful for callers that only want to demonstrate the new theorem-backed
path without supplying meaningful runtime components yet.
-/
def seq_tail_runtime_replay_at_route_ci_of_control_only
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hcontrol : SeqTailControlOnlyConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_control_only_components
    hentry route components hcontrol

/- =========================================================
   Stage 3b: theorem-backed materialization for static-only tails
   ========================================================= -/

/--
Static-only tail shapes whose readiness is constructor-backed from the selected
route's tail static boundary.

The first such case is `declareObj τ x none`: it has no initializer expression,
so it needs no value/place/load/deref replay.  Its readiness follows from the
freshness and object-type evidence contained in the static typing witness.
-/
inductive SeqTailStaticOnlyConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | declareObjNone
      {τ : CppType} {x : Ident} :
      t = .declareObj τ x none →
      SeqTailStaticOnlyConstructorAtRouteCI route

/--
Extract the readiness constructor inputs for `declareObj τ x none` from a
selected tail static boundary.

This is deliberately stated for ordinary `WellTypedFrom`, because
`BodyStaticBoundaryCI.typed0` stores the coarse statement typing surface.
-/
theorem seq_tail_declare_obj_none_ready_of_typed0_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareObj τ x none) σ1 P} :
    StmtReadyConcrete route.Θ σ1 (.declareObj τ x none) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareObjNone hfresh hobj =>
      exact StmtReadyConcrete.declareObjNone hfresh hobj

/--
Materialize tail readiness for the static-only fragment.

This is the second theorem-backed replacement fragment for the coarse
`seq_tail_ready_of_runtime_replay_components_at_route_ci` obligation.
The runtime components are kept in the statement for drop-in compatibility, but
`declareObj none` does not need them.
-/
theorem seq_tail_ready_of_runtime_replay_components_static_only_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstaticOnly : SeqTailStaticOnlyConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hstaticOnly with
  | declareObjNone h =>
      cases h
      exact seq_tail_declare_obj_none_ready_of_typed0_at_route_ci

/--
Assemble the runtime replay package for a static-only tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_static_only_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstaticOnly : SeqTailStaticOnlyConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_static_only_at_route_ci
        hentry route components hstaticOnly }

/--
Convenience constructor for the static-only fragment using the current coarse
component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_static_only
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hstaticOnly : SeqTailStaticOnlyConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_static_only_components
    hentry route components hstaticOnly


/- =========================================================
   Stage 3c: theorem-backed materialization for literal-expression tails
   ========================================================= -/

/--
Literal-expression tail shapes whose readiness is constructor-backed.

These cases are the smallest expression fragment: literals do not read memory,
do not dereference pointers, and do not require alias/readability evidence.
-/
inductive SeqTailLiteralExprConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | exprStmtBool
      {b : Bool} :
      t = .exprStmt (.litBool b) →
      SeqTailLiteralExprConstructorAtRouteCI route
  | exprStmtInt
      {n : Int} :
      t = .exprStmt (.litInt n) →
      SeqTailLiteralExprConstructorAtRouteCI route
  | returnSomeBool
      {b : Bool} :
      t = .returnStmt (some (.litBool b)) →
      SeqTailLiteralExprConstructorAtRouteCI route
  | returnSomeInt
      {n : Int} :
      t = .returnStmt (some (.litInt n)) →
      SeqTailLiteralExprConstructorAtRouteCI route

/--
Materialize tail readiness for the literal-expression fragment.

This is theorem-backed and does not use the broad materialization axiom.  The
runtime components are retained in the statement for a uniform component-based
interface, but literal expressions do not need them.
-/
theorem seq_tail_ready_of_runtime_replay_components_literal_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hlit : SeqTailLiteralExprConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hlit with
  | exprStmtBool h =>
      cases h
      exact
        StmtReadyConcrete.exprStmt
          HasValueType.litBool
          ExprReadyConcrete.litBool
  | exprStmtInt h =>
      cases h
      exact
        StmtReadyConcrete.exprStmt
          HasValueType.litInt
          ExprReadyConcrete.litInt
  | returnSomeBool h =>
      cases h
      exact
        StmtReadyConcrete.returnSome
          HasValueType.litBool
          ExprReadyConcrete.litBool
  | returnSomeInt h =>
      cases h
      exact
        StmtReadyConcrete.returnSome
          HasValueType.litInt
          ExprReadyConcrete.litInt

/--
Assemble the runtime replay package for a literal-expression tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_literal_expr_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hlit : SeqTailLiteralExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_literal_expr_at_route_ci
        hentry route components hlit }

/--
Convenience constructor for the literal-expression fragment using the current
coarse component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_literal_expr
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hlit : SeqTailLiteralExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_literal_expr_components
    hentry route components hlit


/- =========================================================
   Stage 3d: theorem-backed materialization for pure-expression tails
   ========================================================= -/

/--
Pure value-expression replay for the selected tail route.

This fragment deliberately excludes `load`, `addrOf`, and any place/deref case.
It is the memory-independent value-expression fragment, so it can be replayed
at the selected post-state without read-set, deref-pointer, or load-readability
evidence.
-/
inductive SeqTailPureValueExprAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | litBool {b : Bool} :
      SeqTailPureValueExprAtRouteCI route (.litBool b) (.base .bool)
  | litInt {n : Int} :
      SeqTailPureValueExprAtRouteCI route (.litInt n) (.base .int)
  | add {e₁ e₂ : ValExpr} :
      SeqTailPureValueExprAtRouteCI route e₁ (.base .int) →
      SeqTailPureValueExprAtRouteCI route e₂ (.base .int) →
      SeqTailPureValueExprAtRouteCI route (.add e₁ e₂) (.base .int)
  | sub {e₁ e₂ : ValExpr} :
      SeqTailPureValueExprAtRouteCI route e₁ (.base .int) →
      SeqTailPureValueExprAtRouteCI route e₂ (.base .int) →
      SeqTailPureValueExprAtRouteCI route (.sub e₁ e₂) (.base .int)
  | mul {e₁ e₂ : ValExpr} :
      SeqTailPureValueExprAtRouteCI route e₁ (.base .int) →
      SeqTailPureValueExprAtRouteCI route e₂ (.base .int) →
      SeqTailPureValueExprAtRouteCI route (.mul e₁ e₂) (.base .int)
  | eq {e₁ e₂ : ValExpr} {τ : CppType} :
      SeqTailPureValueExprAtRouteCI route e₁ τ →
      SeqTailPureValueExprAtRouteCI route e₂ τ →
      SeqTailPureValueExprAtRouteCI route (.eq e₁ e₂) (.base .bool)
  | lt {e₁ e₂ : ValExpr} :
      SeqTailPureValueExprAtRouteCI route e₁ (.base .int) →
      SeqTailPureValueExprAtRouteCI route e₂ (.base .int) →
      SeqTailPureValueExprAtRouteCI route (.lt e₁ e₂) (.base .bool)
  | not {e : ValExpr} :
      SeqTailPureValueExprAtRouteCI route e (.base .bool) →
      SeqTailPureValueExprAtRouteCI route (.not e) (.base .bool)

namespace SeqTailPureValueExprAtRouteCI

/-- Pure value replay gives the ordinary value typing needed by stmt readiness. -/
theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailPureValueExprAtRouteCI route e τ) :
    HasValueType route.Θ e τ := by
  induction h with
  | litBool =>
      exact HasValueType.litBool
  | litInt =>
      exact HasValueType.litInt
  | add h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.add ih₁ ih₂
  | sub h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.sub ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.mul ih₁ ih₂
  | eq h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.eq ih₁ ih₂
  | lt h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.lt ih₁ ih₂
  | not h ih =>
      exact HasValueType.not ih

/-- Pure value replay gives the expression readiness needed by stmt readiness. -/
theorem exprReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailPureValueExprAtRouteCI route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  induction h with
  | litBool =>
      exact ExprReadyConcrete.litBool
  | litInt =>
      exact ExprReadyConcrete.litInt
  | add h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.add ih₁ ih₂
  | sub h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.sub ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.mul ih₁ ih₂
  | eq h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.eq ih₁ ih₂
  | lt h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.lt ih₁ ih₂
  | not h ih =>
      exact ExprReadyConcrete.not ih

end SeqTailPureValueExprAtRouteCI

/--
Pure-expression tail shapes whose readiness is constructor-backed.

This covers:
* `exprStmt e`
* `returnSome e`
* `declareObjSome τ x e`

for pure value expressions `e`.
-/
inductive SeqTailPureExprConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | exprStmt
      {e : ValExpr} {τ : CppType} :
      SeqTailPureValueExprAtRouteCI route e τ →
      t = .exprStmt e →
      SeqTailPureExprConstructorAtRouteCI route
  | returnSome
      {e : ValExpr} {τ : CppType} :
      SeqTailPureValueExprAtRouteCI route e τ →
      t = .returnStmt (some e) →
      SeqTailPureExprConstructorAtRouteCI route
  | declareObjSome
      {τ : CppType} {x : Ident} {e : ValExpr} :
      SeqTailPureValueExprAtRouteCI route e τ →
      t = .declareObj τ x (some e) →
      SeqTailPureExprConstructorAtRouteCI route

/--
Readiness for `declareObj τ x (some e)` with a pure initializer.

Freshness and object-type evidence are extracted from the selected route's tail
static boundary; the initializer's type/readiness come from pure replay.
-/
theorem seq_tail_declare_obj_some_ready_of_typed0_and_pure_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident} {e : ValExpr}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareObj τ x (some e)) σ1 P}
    (hpure : SeqTailPureValueExprAtRouteCI route e τ) :
    StmtReadyConcrete route.Θ σ1 (.declareObj τ x (some e)) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareObjSome hfresh hobj _htyInit =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh
          hobj
          hpure.hasValueType
          hpure.exprReady

/--
Materialize tail readiness for the pure-expression fragment.

This is theorem-backed and does not use the broad materialization axiom.  Runtime
components are retained in the statement for a uniform component-based
interface, but pure expressions do not need read-set/deref/load replay evidence.
-/
theorem seq_tail_ready_of_runtime_replay_components_pure_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hpureTail : SeqTailPureExprConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hpureTail with
  | exprStmt hpure hshape =>
      cases hshape
      exact
        StmtReadyConcrete.exprStmt
          hpure.hasValueType
          hpure.exprReady
  | returnSome hpure hshape =>
      cases hshape
      exact
        StmtReadyConcrete.returnSome
          hpure.hasValueType
          hpure.exprReady
  | declareObjSome hpure hshape =>
      cases hshape
      exact
        seq_tail_declare_obj_some_ready_of_typed0_and_pure_expr_at_route_ci
          hpure

/--
Assemble the runtime replay package for a pure-expression tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_pure_expr_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hpureTail : SeqTailPureExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_pure_expr_at_route_ci
        hentry route components hpureTail }

/--
Convenience constructor for the pure-expression fragment using the current
coarse component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_pure_expr
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hpureTail : SeqTailPureExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_pure_expr_components
    hentry route components hpureTail


/- =========================================================
   Stage 3e: theorem-backed materialization for ordinary-place tails
   ========================================================= -/

/--
Ordinary variable-place replay for the selected tail route.

This is the first place-level replay fragment.  It intentionally covers only
ordinary variables backed by object/ref bindings.  It does not cover
`PlaceExpr.deref`, because dereference needs pointer-address and live-cell
evidence and belongs to the later deref-pointer stage.
-/
inductive SeqTailPlaceReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    PlaceExpr → CppType → Prop where
  | varObject
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl route.Θ x = some (.object τ) →
      lookupBinding σ1 x = some (.object τ a) →
      CellLiveTyped σ1 a τ →
      SeqTailPlaceReplayAtRouteCI route (.var x) τ
  | varRef
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl route.Θ x = some (.ref τ) →
      lookupBinding σ1 x = some (.ref τ a) →
      CellLiveTyped σ1 a τ →
      SeqTailPlaceReplayAtRouteCI route (.var x) τ

namespace SeqTailPlaceReplayAtRouteCI

/-- Ordinary place replay gives the place typing needed by stmt/expression readiness. -/
theorem hasPlaceType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : SeqTailPlaceReplayAtRouteCI route p τ) :
    HasPlaceType route.Θ p τ := by
  cases h with
  | varObject hdecl hbind hlive =>
      exact HasPlaceType.var hdecl
  | varRef hdecl hbind hlive =>
      exact HasPlaceType.var hdecl

/-- Ordinary place replay gives the concrete place readiness needed by stmt/expression readiness. -/
theorem placeReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : SeqTailPlaceReplayAtRouteCI route p τ) :
    PlaceReadyConcrete route.Θ σ1 p τ := by
  cases h with
  | varObject hdecl hbind hlive =>
      exact PlaceReadyConcrete.varObject hdecl hbind hlive
  | varRef hdecl hbind hlive =>
      exact PlaceReadyConcrete.varRef hdecl hbind hlive

end SeqTailPlaceReplayAtRouteCI

/--
Address-of expression replay for the selected tail route.

`addrOf p` is memory-safe once `p` is a ready place.  It does not load from the
cell, so it does not need load-readability evidence.
-/
inductive SeqTailAddrOfExprAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | addrOf
      {p : PlaceExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      SeqTailAddrOfExprAtRouteCI route (.addrOf p) (.ptr τ)

namespace SeqTailAddrOfExprAtRouteCI

/-- Address-of replay gives value typing. -/
theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailAddrOfExprAtRouteCI route e τ) :
    HasValueType route.Θ e τ := by
  cases h with
  | addrOf hplace =>
      exact HasValueType.addrOf hplace.hasPlaceType

/-- Address-of replay gives expression readiness. -/
theorem exprReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailAddrOfExprAtRouteCI route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  cases h with
  | addrOf hplace =>
      exact ExprReadyConcrete.addrOf hplace.placeReady

end SeqTailAddrOfExprAtRouteCI

/--
Ordinary-place tail shapes whose readiness is constructor-backed.

This covers:
* `exprStmt (addrOf p)`
* `returnSome (addrOf p)`
* `declareObjSome (.ptr τ) x (addrOf p)`
* `declareRef τ x p`
* `assign p e` where `p` is ordinary-place replay and `e` is pure replay
-/
inductive SeqTailPlaceExprConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | exprStmtAddrOf
      {p : PlaceExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      t = .exprStmt (.addrOf p) →
      SeqTailPlaceExprConstructorAtRouteCI route
  | returnSomeAddrOf
      {p : PlaceExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      t = .returnStmt (some (.addrOf p)) →
      SeqTailPlaceExprConstructorAtRouteCI route
  | declareObjSomeAddrOf
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      t = .declareObj (.ptr τ) x (some (.addrOf p)) →
      SeqTailPlaceExprConstructorAtRouteCI route
  | declareRef
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      t = .declareRef τ x p →
      SeqTailPlaceExprConstructorAtRouteCI route
  | assignPure
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      SeqTailPureValueExprAtRouteCI route e τ →
      t = .assign p e →
      SeqTailPlaceExprConstructorAtRouteCI route

/--
Readiness for `declareObj (.ptr τ) x (some (.addrOf p))`.

Freshness and object-type evidence are extracted from the selected route's tail
static boundary; the address-of initializer is supplied by place replay.
-/
theorem seq_tail_declare_obj_some_addr_of_ready_of_typed0_and_place_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident} {p : PlaceExpr}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareObj (.ptr τ) x (some (.addrOf p))) σ1 P}
    (hplace : SeqTailPlaceReplayAtRouteCI route p τ) :
    StmtReadyConcrete route.Θ σ1 (.declareObj (.ptr τ) x (some (.addrOf p))) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareObjSome hfresh hobj _htyInit =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh
          hobj
          (HasValueType.addrOf hplace.hasPlaceType)
          (ExprReadyConcrete.addrOf hplace.placeReady)

/--
Readiness for `declareRef τ x p`.

Freshness is extracted from the selected route's tail static boundary; place
typing and place readiness are supplied by place replay.
-/
theorem seq_tail_declare_ref_ready_of_typed0_and_place_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident} {p : PlaceExpr}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareRef τ x p) σ1 P}
    (hplace : SeqTailPlaceReplayAtRouteCI route p τ) :
    StmtReadyConcrete route.Θ σ1 (.declareRef τ x p) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareRef hfresh _hpty =>
      exact
        StmtReadyConcrete.declareRef
          hfresh
          hplace.hasPlaceType
          hplace.placeReady

/--
Materialize tail readiness for the ordinary-place fragment.

This is theorem-backed and does not use the broad materialization axiom.
-/
theorem seq_tail_ready_of_runtime_replay_components_place_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hplaceTail : SeqTailPlaceExprConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hplaceTail with
  | exprStmtAddrOf hplace hshape =>
      cases hshape
      exact
        StmtReadyConcrete.exprStmt
          (HasValueType.addrOf hplace.hasPlaceType)
          (ExprReadyConcrete.addrOf hplace.placeReady)
  | returnSomeAddrOf hplace hshape =>
      cases hshape
      exact
        StmtReadyConcrete.returnSome
          (HasValueType.addrOf hplace.hasPlaceType)
          (ExprReadyConcrete.addrOf hplace.placeReady)
  | declareObjSomeAddrOf hplace hshape =>
      cases hshape
      exact
        seq_tail_declare_obj_some_addr_of_ready_of_typed0_and_place_at_route_ci
          hplace
  | declareRef hplace hshape =>
      cases hshape
      exact
        seq_tail_declare_ref_ready_of_typed0_and_place_at_route_ci
          hplace
  | assignPure hplace hpure hshape =>
      cases hshape
      exact
        StmtReadyConcrete.assign
          hplace.hasPlaceType
          hplace.placeReady
          hpure.hasValueType
          hpure.exprReady

/--
Assemble the runtime replay package for an ordinary-place tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_place_expr_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hplaceTail : SeqTailPlaceExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_place_expr_at_route_ci
        hentry route components hplaceTail }

/--
Convenience constructor for the ordinary-place fragment using the current coarse
component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_place_expr
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hplaceTail : SeqTailPlaceExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_place_expr_components
    hentry route components hplaceTail


/- =========================================================
   Stage 3f: theorem-backed materialization for load-expression tails
   ========================================================= -/

/--
Load-value replay for the selected tail route.

This is the first stage that uses the load-readability idea for real.  A load is
ready when its source place is ready and the concrete post-state contains a
readable typed cell at the address reached by that place.

This deliberately reuses the ordinary-place replay from stage 3e.  Therefore
this stage covers `load p` for ordinary variable places, but still avoids
`PlaceExpr.deref`, which belongs to the later deref-pointer stage.
-/
inductive SeqTailLoadValueExprAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | load
      {p : PlaceExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      (∃ a, BigStepPlace σ1 p a ∧ CellReadableTyped σ1 a τ) →
      SeqTailLoadValueExprAtRouteCI route (.load p) τ

namespace SeqTailLoadValueExprAtRouteCI

/-- Load replay gives value typing. -/
theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailLoadValueExprAtRouteCI route e τ) :
    HasValueType route.Θ e τ := by
  cases h with
  | load hplace hread =>
      exact HasValueType.load hplace.hasPlaceType

/-- Load replay gives expression readiness. -/
theorem exprReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailLoadValueExprAtRouteCI route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  cases h with
  | load hplace hread =>
      exact ExprReadyConcrete.load hplace.placeReady hread

end SeqTailLoadValueExprAtRouteCI

/--
Load-expression tail shapes whose readiness is constructor-backed.

This covers:
* `exprStmt (load p)`
* `returnSome (load p)`
* `declareObjSome τ x (load p)`
* `assign q (load p)` where `q` is ordinary-place replay
-/
inductive SeqTailLoadExprConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | exprStmtLoad
      {p : PlaceExpr} {τ : CppType} :
      SeqTailLoadValueExprAtRouteCI route (.load p) τ →
      t = .exprStmt (.load p) →
      SeqTailLoadExprConstructorAtRouteCI route
  | returnSomeLoad
      {p : PlaceExpr} {τ : CppType} :
      SeqTailLoadValueExprAtRouteCI route (.load p) τ →
      t = .returnStmt (some (.load p)) →
      SeqTailLoadExprConstructorAtRouteCI route
  | declareObjSomeLoad
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      SeqTailLoadValueExprAtRouteCI route (.load p) τ →
      t = .declareObj τ x (some (.load p)) →
      SeqTailLoadExprConstructorAtRouteCI route
  | assignLoadRhs
      {q p : PlaceExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route q τ →
      SeqTailLoadValueExprAtRouteCI route (.load p) τ →
      t = .assign q (.load p) →
      SeqTailLoadExprConstructorAtRouteCI route

/--
Readiness for `declareObj τ x (some (load p))`.

Freshness and object-type evidence are extracted from the selected route's tail
static boundary; the initializer's type/readiness come from load replay.
-/
theorem seq_tail_declare_obj_some_load_ready_of_typed0_and_load_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident} {p : PlaceExpr}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareObj τ x (some (.load p))) σ1 P}
    (hload : SeqTailLoadValueExprAtRouteCI route (.load p) τ) :
    StmtReadyConcrete route.Θ σ1 (.declareObj τ x (some (.load p))) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareObjSome hfresh hobj _htyInit =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh
          hobj
          hload.hasValueType
          hload.exprReady

/--
Materialize tail readiness for the load-expression fragment.

This is theorem-backed and does not use the broad materialization axiom.
-/
theorem seq_tail_ready_of_runtime_replay_components_load_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hloadTail : SeqTailLoadExprConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hloadTail with
  | exprStmtLoad hload hshape =>
      cases hshape
      exact
        StmtReadyConcrete.exprStmt
          hload.hasValueType
          hload.exprReady
  | returnSomeLoad hload hshape =>
      cases hshape
      exact
        StmtReadyConcrete.returnSome
          hload.hasValueType
          hload.exprReady
  | declareObjSomeLoad hload hshape =>
      cases hshape
      exact
        seq_tail_declare_obj_some_load_ready_of_typed0_and_load_at_route_ci
          hload
  | assignLoadRhs htarget hload hshape =>
      cases hshape
      exact
        StmtReadyConcrete.assign
          htarget.hasPlaceType
          htarget.placeReady
          hload.hasValueType
          hload.exprReady

/--
Assemble the runtime replay package for a load-expression tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_load_expr_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hloadTail : SeqTailLoadExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_load_expr_at_route_ci
        hentry route components hloadTail }

/--
Convenience constructor for the load-expression fragment using the current
coarse component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_load_expr
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hloadTail : SeqTailLoadExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_load_expr_components
    hentry route components hloadTail


/- =========================================================
   Stage 3g: theorem-backed materialization for dereference-place tails
   ========================================================= -/

/--
Dereference-place replay for the selected tail route.

This is the first stage that uses the pointer-dereference idea for real.  A
deref place is ready exactly when the pointer expression evaluates to an address
and the addressed cell is live and typed in the selected post-state.
-/
inductive SeqTailDerefPlaceReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    PlaceExpr → CppType → Prop where
  | deref
      {e : ValExpr} {τ : CppType} {a : Nat} :
      PtrValueReadyAt route.Θ σ1 e τ a →
      CellLiveTyped σ1 a τ →
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ

namespace SeqTailDerefPlaceReplayAtRouteCI

/-- Dereference replay gives the place typing needed by stmt/expression readiness. -/
theorem hasPlaceType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : SeqTailDerefPlaceReplayAtRouteCI route p τ) :
    HasPlaceType route.Θ p τ := by
  cases h with
  | deref hptr hlive =>
      exact HasPlaceType.deref hptr.1

/-- Dereference replay gives the concrete place readiness needed by stmt/expression readiness. -/
theorem placeReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : SeqTailDerefPlaceReplayAtRouteCI route p τ) :
    PlaceReadyConcrete route.Θ σ1 p τ := by
  cases h with
  | deref hptr hlive =>
      exact PlaceReadyConcrete.deref hptr hlive

end SeqTailDerefPlaceReplayAtRouteCI

/--
Address-of over a dereference place.

Taking the address of a ready dereference place does not load from the cell, but
it does require that the dereference place itself is valid/live/typed.
-/
inductive SeqTailAddrOfDerefExprAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | addrOfDeref
      {e : ValExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      SeqTailAddrOfDerefExprAtRouteCI route (.addrOf (.deref e)) (.ptr τ)

namespace SeqTailAddrOfDerefExprAtRouteCI

/-- Address-of-deref replay gives value typing. -/
theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailAddrOfDerefExprAtRouteCI route e τ) :
    HasValueType route.Θ e τ := by
  cases h with
  | addrOfDeref hderef =>
      exact HasValueType.addrOf hderef.hasPlaceType

/-- Address-of-deref replay gives expression readiness. -/
theorem exprReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailAddrOfDerefExprAtRouteCI route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  cases h with
  | addrOfDeref hderef =>
      exact ExprReadyConcrete.addrOf hderef.placeReady

end SeqTailAddrOfDerefExprAtRouteCI

/--
Dereference-place tail shapes whose readiness is constructor-backed.

This covers:
* `exprStmt (addrOf (deref e))`
* `returnSome (addrOf (deref e))`
* `declareObjSome (.ptr τ) x (addrOf (deref e))`
* `declareRef τ x (deref e)`
* `assign (deref e) rhs` where rhs is pure replay
* `assign q (addrOf (deref e))` where q is an ordinary place of pointer type
-/
inductive SeqTailDerefExprConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | exprStmtAddrOfDeref
      {e : ValExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      t = .exprStmt (.addrOf (.deref e)) →
      SeqTailDerefExprConstructorAtRouteCI route
  | returnSomeAddrOfDeref
      {e : ValExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      t = .returnStmt (some (.addrOf (.deref e))) →
      SeqTailDerefExprConstructorAtRouteCI route
  | declareObjSomeAddrOfDeref
      {τ : CppType} {x : Ident} {e : ValExpr} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      t = .declareObj (.ptr τ) x (some (.addrOf (.deref e))) →
      SeqTailDerefExprConstructorAtRouteCI route
  | declareRefDeref
      {τ : CppType} {x : Ident} {e : ValExpr} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      t = .declareRef τ x (.deref e) →
      SeqTailDerefExprConstructorAtRouteCI route
  | assignDerefLhsPure
      {ePtr rhs : ValExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref ePtr) τ →
      SeqTailPureValueExprAtRouteCI route rhs τ →
      t = .assign (.deref ePtr) rhs →
      SeqTailDerefExprConstructorAtRouteCI route
  | assignAddrOfDerefRhs
      {q : PlaceExpr} {e : ValExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route q (.ptr τ) →
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      t = .assign q (.addrOf (.deref e)) →
      SeqTailDerefExprConstructorAtRouteCI route

/--
Readiness for `declareObj (.ptr τ) x (some (addrOf (deref e)))`.

Freshness and object-type evidence are extracted from the selected route's tail
static boundary; address-of-deref readiness comes from deref-place replay.
-/
theorem seq_tail_declare_obj_some_addr_of_deref_ready_of_typed0_and_deref_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident} {e : ValExpr}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareObj (.ptr τ) x (some (.addrOf (.deref e)))) σ1 P}
    (hderef : SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ) :
    StmtReadyConcrete route.Θ σ1 (.declareObj (.ptr τ) x (some (.addrOf (.deref e)))) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareObjSome hfresh hobj _htyInit =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh
          hobj
          (HasValueType.addrOf hderef.hasPlaceType)
          (ExprReadyConcrete.addrOf hderef.placeReady)

/--
Readiness for `declareRef τ x (deref e)`.

Freshness is extracted from the selected route's tail static boundary; deref
place typing/readiness comes from deref-place replay.
-/
theorem seq_tail_declare_ref_deref_ready_of_typed0_and_deref_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident} {e : ValExpr}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareRef τ x (.deref e)) σ1 P}
    (hderef : SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ) :
    StmtReadyConcrete route.Θ σ1 (.declareRef τ x (.deref e)) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareRef hfresh _hpty =>
      exact
        StmtReadyConcrete.declareRef
          hfresh
          hderef.hasPlaceType
          hderef.placeReady

/--
Materialize tail readiness for the dereference-place fragment.

This is theorem-backed and does not use the broad materialization axiom.
-/
theorem seq_tail_ready_of_runtime_replay_components_deref_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hderefTail : SeqTailDerefExprConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hderefTail with
  | exprStmtAddrOfDeref hderef hshape =>
      cases hshape
      exact
        StmtReadyConcrete.exprStmt
          (HasValueType.addrOf hderef.hasPlaceType)
          (ExprReadyConcrete.addrOf hderef.placeReady)
  | returnSomeAddrOfDeref hderef hshape =>
      cases hshape
      exact
        StmtReadyConcrete.returnSome
          (HasValueType.addrOf hderef.hasPlaceType)
          (ExprReadyConcrete.addrOf hderef.placeReady)
  | declareObjSomeAddrOfDeref hderef hshape =>
      cases hshape
      exact
        seq_tail_declare_obj_some_addr_of_deref_ready_of_typed0_and_deref_at_route_ci
          hderef
  | declareRefDeref hderef hshape =>
      cases hshape
      exact
        seq_tail_declare_ref_deref_ready_of_typed0_and_deref_at_route_ci
          hderef
  | assignDerefLhsPure hderef hpure hshape =>
      cases hshape
      exact
        StmtReadyConcrete.assign
          hderef.hasPlaceType
          hderef.placeReady
          hpure.hasValueType
          hpure.exprReady
  | assignAddrOfDerefRhs htarget hderef hshape =>
      cases hshape
      exact
        StmtReadyConcrete.assign
          htarget.hasPlaceType
          htarget.placeReady
          (HasValueType.addrOf hderef.hasPlaceType)
          (ExprReadyConcrete.addrOf hderef.placeReady)

/--
Assemble the runtime replay package for a dereference-place tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_deref_expr_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hderefTail : SeqTailDerefExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_deref_expr_at_route_ci
        hentry route components hderefTail }

/--
Convenience constructor for the dereference-place fragment using the current
coarse component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_deref_expr
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hderefTail : SeqTailDerefExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_deref_expr_components
    hentry route components hderefTail


/- =========================================================
   Stage 3h: theorem-backed materialization for mixed value expressions
   ========================================================= -/

/--
Mixed value-expression replay for the selected tail route.

This unifies the previous expression fragments:
* pure expressions from stage 3d;
* load expressions from stage 3f;
* address-of ordinary places from stage 3e;
* address-of dereference places from stage 3g;
* recursive arithmetic/comparison/boolean combinators.

The point is to make mixed expressions theorem-backed without immediately
moving to statement-level replay distribution.
-/
inductive SeqTailValueExprReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | pure
      {e : ValExpr} {τ : CppType} :
      SeqTailPureValueExprAtRouteCI route e τ →
      SeqTailValueExprReplayAtRouteCI route e τ
  | load
      {e : ValExpr} {τ : CppType} :
      SeqTailLoadValueExprAtRouteCI route e τ →
      SeqTailValueExprReplayAtRouteCI route e τ
  | addrOfPlace
      {p : PlaceExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      SeqTailValueExprReplayAtRouteCI route (.addrOf p) (.ptr τ)
  | addrOfDeref
      {e : ValExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      SeqTailValueExprReplayAtRouteCI route (.addrOf (.deref e)) (.ptr τ)
  | add
      {e₁ e₂ : ValExpr} :
      SeqTailValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route (.add e₁ e₂) (.base .int)
  | sub
      {e₁ e₂ : ValExpr} :
      SeqTailValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route (.sub e₁ e₂) (.base .int)
  | mul
      {e₁ e₂ : ValExpr} :
      SeqTailValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route (.mul e₁ e₂) (.base .int)
  | eq
      {e₁ e₂ : ValExpr} {τ : CppType} :
      SeqTailValueExprReplayAtRouteCI route e₁ τ →
      SeqTailValueExprReplayAtRouteCI route e₂ τ →
      SeqTailValueExprReplayAtRouteCI route (.eq e₁ e₂) (.base .bool)
  | lt
      {e₁ e₂ : ValExpr} :
      SeqTailValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailValueExprReplayAtRouteCI route (.lt e₁ e₂) (.base .bool)
  | not
      {e : ValExpr} :
      SeqTailValueExprReplayAtRouteCI route e (.base .bool) →
      SeqTailValueExprReplayAtRouteCI route (.not e) (.base .bool)

namespace SeqTailValueExprReplayAtRouteCI

/-- Mixed value-expression replay gives ordinary value typing. -/
theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailValueExprReplayAtRouteCI route e τ) :
    HasValueType route.Θ e τ := by
  induction h with
  | pure hpure =>
      exact hpure.hasValueType
  | load hload =>
      exact hload.hasValueType
  | addrOfPlace hplace =>
      exact HasValueType.addrOf hplace.hasPlaceType
  | addrOfDeref hderef =>
      exact HasValueType.addrOf hderef.hasPlaceType
  | add h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.add ih₁ ih₂
  | sub h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.sub ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.mul ih₁ ih₂
  | eq h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.eq ih₁ ih₂
  | lt h₁ h₂ ih₁ ih₂ =>
      exact HasValueType.lt ih₁ ih₂
  | not h ih =>
      exact HasValueType.not ih

/-- Mixed value-expression replay gives expression readiness. -/
theorem exprReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailValueExprReplayAtRouteCI route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  induction h with
  | pure hpure =>
      exact hpure.exprReady
  | load hload =>
      exact hload.exprReady
  | addrOfPlace hplace =>
      exact ExprReadyConcrete.addrOf hplace.placeReady
  | addrOfDeref hderef =>
      exact ExprReadyConcrete.addrOf hderef.placeReady
  | add h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.add ih₁ ih₂
  | sub h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.sub ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.mul ih₁ ih₂
  | eq h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.eq ih₁ ih₂
  | lt h₁ h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.lt ih₁ ih₂
  | not h ih =>
      exact ExprReadyConcrete.not ih

end SeqTailValueExprReplayAtRouteCI

/--
Mixed value-expression tail shapes whose readiness is constructor-backed.

This covers:
* `exprStmt e`
* `returnSome e`
* `declareObjSome τ x e`
* `assign p e`, where `p` is ordinary-place replay;
* `assign (deref eptr) e`, where deref-place replay is available.
-/
inductive SeqTailValueExprConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | exprStmt
      {e : ValExpr} {τ : CppType} :
      SeqTailValueExprReplayAtRouteCI route e τ →
      t = .exprStmt e →
      SeqTailValueExprConstructorAtRouteCI route
  | returnSome
      {e : ValExpr} {τ : CppType} :
      SeqTailValueExprReplayAtRouteCI route e τ →
      t = .returnStmt (some e) →
      SeqTailValueExprConstructorAtRouteCI route
  | declareObjSome
      {τ : CppType} {x : Ident} {e : ValExpr} :
      SeqTailValueExprReplayAtRouteCI route e τ →
      t = .declareObj τ x (some e) →
      SeqTailValueExprConstructorAtRouteCI route
  | assignOrdinary
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      SeqTailValueExprReplayAtRouteCI route e τ →
      t = .assign p e →
      SeqTailValueExprConstructorAtRouteCI route
  | assignDeref
      {eptr rhs : ValExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref eptr) τ →
      SeqTailValueExprReplayAtRouteCI route rhs τ →
      t = .assign (.deref eptr) rhs →
      SeqTailValueExprConstructorAtRouteCI route

/--
Readiness for `declareObj τ x (some e)` with a mixed value-expression
initializer.

Freshness and object-type evidence are extracted from the selected route's tail
static boundary; the initializer's type/readiness come from value-expression
replay.
-/
theorem seq_tail_declare_obj_some_ready_of_typed0_and_value_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {τ : CppType} {x : Ident} {e : ValExpr}
    {route : SeqHeadNormalRouteCI Γ σ s (.declareObj τ x (some e)) σ1 P}
    (hvalue : SeqTailValueExprReplayAtRouteCI route e τ) :
    StmtReadyConcrete route.Θ σ1 (.declareObj τ x (some e)) := by
  rcases route.tail.static.typed0 with ⟨Δ, hty⟩
  cases hty with
  | declareObjSome hfresh hobj _htyInit =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh
          hobj
          hvalue.hasValueType
          hvalue.exprReady

/--
Materialize tail readiness for the mixed value-expression fragment.

This is theorem-backed and does not use the broad materialization axiom.
-/
theorem seq_tail_ready_of_runtime_replay_components_value_expr_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hvalueTail : SeqTailValueExprConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hvalueTail with
  | exprStmt hvalue hshape =>
      cases hshape
      exact
        StmtReadyConcrete.exprStmt
          hvalue.hasValueType
          hvalue.exprReady
  | returnSome hvalue hshape =>
      cases hshape
      exact
        StmtReadyConcrete.returnSome
          hvalue.hasValueType
          hvalue.exprReady
  | declareObjSome hvalue hshape =>
      cases hshape
      exact
        seq_tail_declare_obj_some_ready_of_typed0_and_value_expr_at_route_ci
          hvalue
  | assignOrdinary hplace hvalue hshape =>
      cases hshape
      exact
        StmtReadyConcrete.assign
          hplace.hasPlaceType
          hplace.placeReady
          hvalue.hasValueType
          hvalue.exprReady
  | assignDeref hderef hvalue hshape =>
      cases hshape
      exact
        StmtReadyConcrete.assign
          hderef.hasPlaceType
          hderef.placeReady
          hvalue.hasValueType
          hvalue.exprReady

/--
Assemble the runtime replay package for a mixed value-expression tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_value_expr_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hvalueTail : SeqTailValueExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_value_expr_at_route_ci
        hentry route components hvalueTail }

/--
Convenience constructor for the mixed value-expression fragment using the
current coarse component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_value_expr
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hvalueTail : SeqTailValueExprConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_value_expr_components
    hentry route components hvalueTail


/- =========================================================
   Stage 3i: theorem-backed materialization for statement replay
   ========================================================= -/

/--
Assignable/place replay for statement-level replay.

This unifies ordinary variable places from stage 3e and dereference places from
stage 3g.  It is exactly the amount of information needed by statement
constructors such as `assign` and `declareRef`.
-/
inductive SeqTailAnyPlaceReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    PlaceExpr → CppType → Prop where
  | ordinary
      {p : PlaceExpr} {τ : CppType} :
      SeqTailPlaceReplayAtRouteCI route p τ →
      SeqTailAnyPlaceReplayAtRouteCI route p τ
  | deref
      {p : PlaceExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route p τ →
      SeqTailAnyPlaceReplayAtRouteCI route p τ

namespace SeqTailAnyPlaceReplayAtRouteCI

/-- Any place replay gives place typing. -/
theorem hasPlaceType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : SeqTailAnyPlaceReplayAtRouteCI route p τ) :
    HasPlaceType route.Θ p τ := by
  cases h with
  | ordinary hplace =>
      exact hplace.hasPlaceType
  | deref hderef =>
      exact hderef.hasPlaceType

/-- Any place replay gives concrete place readiness. -/
theorem placeReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : SeqTailAnyPlaceReplayAtRouteCI route p τ) :
    PlaceReadyConcrete route.Θ σ1 p τ := by
  cases h with
  | ordinary hplace =>
      exact hplace.placeReady
  | deref hderef =>
      exact hderef.placeReady

end SeqTailAnyPlaceReplayAtRouteCI

/--
Statement replay for the selected tail route.

This is the first statement-level distribution predicate.  It intentionally
starts with `seq` and `ite`, because those are direct constructors of
`StmtReadyConcrete`.  `while` and `block` are left for later stages.
-/
inductive SeqTailStmtReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    CppStmt → Prop where
  | skip :
      SeqTailStmtReplayAtRouteCI route .skip
  | breakStmt :
      SeqTailStmtReplayAtRouteCI route .breakStmt
  | continueStmt :
      SeqTailStmtReplayAtRouteCI route .continueStmt
  | returnNone :
      SeqTailStmtReplayAtRouteCI route (.returnStmt none)
  | exprStmt
      {e : ValExpr} {τ : CppType} :
      SeqTailValueExprReplayAtRouteCI route e τ →
      SeqTailStmtReplayAtRouteCI route (.exprStmt e)
  | returnSome
      {e : ValExpr} {τ : CppType} :
      SeqTailValueExprReplayAtRouteCI route e τ →
      SeqTailStmtReplayAtRouteCI route (.returnStmt (some e))
  | declareObjNone
      {τ : CppType} {x : Ident} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      SeqTailStmtReplayAtRouteCI route (.declareObj τ x none)
  | declareObjSome
      {τ : CppType} {x : Ident} {e : ValExpr} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      SeqTailValueExprReplayAtRouteCI route e τ →
      SeqTailStmtReplayAtRouteCI route (.declareObj τ x (some e))
  | declareRef
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh route.Θ x →
      SeqTailAnyPlaceReplayAtRouteCI route p τ →
      SeqTailStmtReplayAtRouteCI route (.declareRef τ x p)
  | assign
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      SeqTailAnyPlaceReplayAtRouteCI route p τ →
      SeqTailValueExprReplayAtRouteCI route e τ →
      SeqTailStmtReplayAtRouteCI route (.assign p e)
  | seq
      {u v : CppStmt} :
      SeqTailStmtReplayAtRouteCI route u →
      SeqTailStmtReplayAtRouteCI route v →
      SeqTailStmtReplayAtRouteCI route (.seq u v)
  | ite
      {c : ValExpr} {u v : CppStmt} :
      SeqTailValueExprReplayAtRouteCI route c (.base .bool) →
      SeqTailStmtReplayAtRouteCI route u →
      SeqTailStmtReplayAtRouteCI route v →
      SeqTailStmtReplayAtRouteCI route (.ite c u v)

namespace SeqTailStmtReplayAtRouteCI

/--
Statement replay materializes ordinary statement readiness.

This is the first theorem that distributes replay through statement constructors
rather than only recognizing top-level statement shapes.
-/
theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {st : CppStmt}
    (h : SeqTailStmtReplayAtRouteCI route st) :
    StmtReadyConcrete route.Θ σ1 st := by
  induction h with
  | skip =>
      exact StmtReadyConcrete.skip
  | breakStmt =>
      exact StmtReadyConcrete.breakStmt
  | continueStmt =>
      exact StmtReadyConcrete.continueStmt
  | returnNone =>
      exact StmtReadyConcrete.returnNone
  | exprStmt hvalue =>
      exact
        StmtReadyConcrete.exprStmt
          hvalue.hasValueType
          hvalue.exprReady
  | returnSome hvalue =>
      exact
        StmtReadyConcrete.returnSome
          hvalue.hasValueType
          hvalue.exprReady
  | declareObjNone hfresh hobj =>
      exact StmtReadyConcrete.declareObjNone hfresh hobj
  | declareObjSome hfresh hobj hvalue =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh
          hobj
          hvalue.hasValueType
          hvalue.exprReady
  | declareRef hfresh hplace =>
      exact
        StmtReadyConcrete.declareRef
          hfresh
          hplace.hasPlaceType
          hplace.placeReady
  | assign hplace hvalue =>
      exact
        StmtReadyConcrete.assign
          hplace.hasPlaceType
          hplace.placeReady
          hvalue.hasValueType
          hvalue.exprReady
  | seq hu hv ihu ihv =>
      exact StmtReadyConcrete.seq ihu ihv
  | ite hc hu hv ihU ihV =>
      exact
        StmtReadyConcrete.ite
          hc.hasValueType
          hc.exprReady
          ihU
          ihV

end SeqTailStmtReplayAtRouteCI

/--
Tail shape for statement-level replay.

This wrapper keeps the same route-indexed top-level style as the earlier stage
fragments while allowing the replay proof to be recursive in the statement.
-/
inductive SeqTailStmtReplayConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | ofReplay :
      SeqTailStmtReplayAtRouteCI route t →
      SeqTailStmtReplayConstructorAtRouteCI route

/--
Materialize tail readiness from statement-level replay.

This is theorem-backed and does not use the broad materialization axiom.
-/
theorem seq_tail_ready_of_runtime_replay_components_stmt_replay_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstmt : SeqTailStmtReplayConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hstmt with
  | ofReplay hreplay =>
      exact hreplay.ready

/--
Assemble the runtime replay package from statement-level replay.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_stmt_replay_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstmt : SeqTailStmtReplayConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_stmt_replay_at_route_ci
        hentry route components hstmt }

/--
Convenience constructor for statement-level replay using the current coarse
component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_stmt_replay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hstmt : SeqTailStmtReplayConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_stmt_replay_components
    hentry route components hstmt


/--
Materialize tail readiness from the named runtime replay components.

This is intentionally still an obligation.  The progress is that the obligation
is no longer "transport readiness after normal"; it is now "these concrete
runtime replay components are sufficient for the selected route's tail
readiness".
-/
axiom seq_tail_ready_of_runtime_replay_components_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t

/-- Assemble the runtime replay package from named replay components. -/
def seq_tail_runtime_replay_at_route_ci_of_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_at_route_ci
        hentry route components }

/--
Compared with the previous coarse version, this now has three visible layers:

* `postStatePart`: preservation-shaped post-state/environment agreement;
* `nameScopePart`: static/name/scope side of the selected tail;
* `runtimePart`: runtime replay/readiness side, with future C++ split points.

The important change is that the public subject is still the selected route,
not a global exact-tail readiness transport theorem.
-/
structure SeqTailStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  postStatePart : SeqTailPostStateAtRouteCI route
  nameScopePart : SeqTailNameScopeStabilityAtRouteCI route
  runtimePart : SeqTailRuntimeReplayAtRouteCI route

namespace SeqTailNameScopeStabilityAtRouteCI

/-- The current selected route already carries the coarse tail typing witness. -/
def ofRoute
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailNameScopeStabilityAtRouteCI route :=
  { typed0 := route.tail.static.typed0 }

end SeqTailNameScopeStabilityAtRouteCI

namespace SeqTailStabilityAtRouteCI

/-- Post-state projection preserved for old callers. -/
def postState
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    ScopedTypedStateConcrete route.Θ σ1 :=
  h.postStatePart.postState

/-- Runtime tail-readiness projection preserved for old callers. -/
def tailReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t :=
  h.runtimePart.tailReady

/-- The dynamic continuation boundary induced by a route-local stability proof. -/
def toStmtContinuationDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  { state := h.postState
    safe := h.tailReady }

/-- Compatibility view as the old body dynamic boundary. -/
def toBodyDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    BodyDynamicBoundary route.Θ σ1 t :=
  h.toStmtContinuationDynamicBoundary.toBodyDynamicBoundary

end SeqTailStabilityAtRouteCI

/--
Assemble the route-local stability contract from its preservation/static/runtime
parts.

This is the preferred constructor for the next stage: callers should eventually
supply post-state preservation and runtime replay separately.
-/
def seq_tail_stability_at_route_ci_of_parts
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (postState : SeqTailPostStateAtRouteCI route)
    (runtime : SeqTailRuntimeReplayAtRouteCI route) :
    SeqTailStabilityAtRouteCI route :=
  { postStatePart := postState
    nameScopePart := SeqTailNameScopeStabilityAtRouteCI.ofRoute route
    runtimePart := runtime }

end Cpp
