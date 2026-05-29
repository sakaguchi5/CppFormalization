import CppFormalization.Cpp2.Stability.Replay.SeqTail.Place

namespace Cpp

/-!
# Seq tail replay: load-expression materialization
-/

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

end Cpp
