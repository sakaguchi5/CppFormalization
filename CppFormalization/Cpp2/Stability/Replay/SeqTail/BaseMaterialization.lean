import CppFormalization.Cpp2.Stability.Replay.SeqTail.RuntimeComponents

namespace Cpp

/-!
# Seq tail replay: base materialization fragments
-/

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

end Cpp
