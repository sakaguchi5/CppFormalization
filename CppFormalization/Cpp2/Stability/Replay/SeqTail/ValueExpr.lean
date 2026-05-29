import CppFormalization.Cpp2.Stability.Replay.SeqTail.Deref

namespace Cpp

/-!
# Seq tail replay: mixed value-expression materialization
-/

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

end Cpp
