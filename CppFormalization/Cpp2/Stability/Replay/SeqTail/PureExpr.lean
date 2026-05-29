import CppFormalization.Cpp2.Stability.Replay.SeqTail.RuntimeComponents

namespace Cpp

/-!
# Seq tail replay: pure-expression materialization
-/

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

end Cpp
