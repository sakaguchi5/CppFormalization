import CppFormalization.Cpp2.Stability.Replay.SeqTail.Load

namespace Cpp

/-!
# Seq tail replay: dereference-place materialization
-/

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

end Cpp
