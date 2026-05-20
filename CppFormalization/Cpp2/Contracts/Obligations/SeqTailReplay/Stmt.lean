import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.ValueExpr

namespace Cpp

/-!
# Seq tail replay: statement-level replay
-/

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

end Cpp
