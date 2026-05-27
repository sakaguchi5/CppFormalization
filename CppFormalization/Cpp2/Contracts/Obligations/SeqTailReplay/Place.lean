import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.PureExpr

namespace Cpp

/-!
# Seq tail replay: ordinary-place materialization
-/

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

end Cpp
