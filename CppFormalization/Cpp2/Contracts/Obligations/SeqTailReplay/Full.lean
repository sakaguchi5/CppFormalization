import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Structured

namespace Cpp

/-!
# Seq tail replay: full integration API

This module is the first post-split integration layer.  It introduces the main
theorem-backed replacement API while keeping the broad fallback axiom available
in `Stability.lean`.
-/

/--
Load over a dereference place.

This combines deref-pointer safety and load-readability safety for
`load (deref e)`.
-/
inductive SeqTailLoadDerefValueExprAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | loadDeref
      {e : ValExpr} {τ : CppType} :
      SeqTailDerefPlaceReplayAtRouteCI route (.deref e) τ →
      (∃ a, BigStepPlace σ1 (.deref e) a ∧ CellReadableTyped σ1 a τ) →
      SeqTailLoadDerefValueExprAtRouteCI route (.load (.deref e)) τ

namespace SeqTailLoadDerefValueExprAtRouteCI

theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailLoadDerefValueExprAtRouteCI route e τ) :
    HasValueType route.Θ e τ := by
  cases h with
  | loadDeref hderef hread =>
      exact HasValueType.load hderef.hasPlaceType

theorem exprReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailLoadDerefValueExprAtRouteCI route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  cases h with
  | loadDeref hderef hread =>
      exact ExprReadyConcrete.load hderef.placeReady hread

end SeqTailLoadDerefValueExprAtRouteCI

/--
Full value-expression replay for the selected tail route.

This extends `SeqTailValueExprReplayAtRouteCI` with `load (deref e)` and keeps
the recursive arithmetic/comparison/boolean closure.
-/
inductive SeqTailFullValueExprReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | base
      {e : ValExpr} {τ : CppType} :
      SeqTailValueExprReplayAtRouteCI route e τ →
      SeqTailFullValueExprReplayAtRouteCI route e τ
  | loadDeref
      {e : ValExpr} {τ : CppType} :
      SeqTailLoadDerefValueExprAtRouteCI route e τ →
      SeqTailFullValueExprReplayAtRouteCI route e τ
  | add
      {e₁ e₂ : ValExpr} :
      SeqTailFullValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route (.add e₁ e₂) (.base .int)
  | sub
      {e₁ e₂ : ValExpr} :
      SeqTailFullValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route (.sub e₁ e₂) (.base .int)
  | mul
      {e₁ e₂ : ValExpr} :
      SeqTailFullValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route (.mul e₁ e₂) (.base .int)
  | eq
      {e₁ e₂ : ValExpr} {τ : CppType} :
      SeqTailFullValueExprReplayAtRouteCI route e₁ τ →
      SeqTailFullValueExprReplayAtRouteCI route e₂ τ →
      SeqTailFullValueExprReplayAtRouteCI route (.eq e₁ e₂) (.base .bool)
  | lt
      {e₁ e₂ : ValExpr} :
      SeqTailFullValueExprReplayAtRouteCI route e₁ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route e₂ (.base .int) →
      SeqTailFullValueExprReplayAtRouteCI route (.lt e₁ e₂) (.base .bool)
  | not
      {e : ValExpr} :
      SeqTailFullValueExprReplayAtRouteCI route e (.base .bool) →
      SeqTailFullValueExprReplayAtRouteCI route (.not e) (.base .bool)

namespace SeqTailFullValueExprReplayAtRouteCI

theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailFullValueExprReplayAtRouteCI route e τ) :
    HasValueType route.Θ e τ := by
  induction h with
  | base hbase =>
      exact hbase.hasValueType
  | loadDeref hload =>
      exact hload.hasValueType
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

theorem exprReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : SeqTailFullValueExprReplayAtRouteCI route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  induction h with
  | base hbase =>
      exact hbase.exprReady
  | loadDeref hload =>
      exact hload.exprReady
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

end SeqTailFullValueExprReplayAtRouteCI

/--
Full block replay for the selected tail route.

This remains conservative: block-local statements live under pushed scopes, so
the `cons` constructor takes pushed-scope readiness directly.
-/
inductive SeqTailFullBlockReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    StmtBlock → Prop where
  | nil :
      SeqTailFullBlockReplayAtRouteCI route .nil
  | cons
      {st : CppStmt} {ss : StmtBlock} :
      StmtReadyConcrete (pushTypeScope route.Θ) (pushScope σ1) st →
      SeqTailFullBlockReplayAtRouteCI route ss →
      SeqTailFullBlockReplayAtRouteCI route (.cons st ss)
  | existing
      {ss : StmtBlock} :
      SeqTailBlockReplayAtRouteCI route ss →
      SeqTailFullBlockReplayAtRouteCI route ss

namespace SeqTailFullBlockReplayAtRouteCI

theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {ss : StmtBlock}
    (h : SeqTailFullBlockReplayAtRouteCI route ss) :
    BlockReadyConcrete (pushTypeScope route.Θ) (pushScope σ1) ss := by
  induction h with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hst hss ih =>
      exact BlockReadyConcrete.cons hst ih
  | existing hblock =>
      exact hblock.ready

end SeqTailFullBlockReplayAtRouteCI

/--
Full statement replay for the selected tail route.

This is the integrated statement replay API.
-/
inductive SeqTailFullStmtReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    CppStmt → Prop where
  | existing
      {st : CppStmt} :
      SeqTailStmtReplayAtRouteCI route st →
      SeqTailFullStmtReplayAtRouteCI route st
  | skip :
      SeqTailFullStmtReplayAtRouteCI route .skip
  | breakStmt :
      SeqTailFullStmtReplayAtRouteCI route .breakStmt
  | continueStmt :
      SeqTailFullStmtReplayAtRouteCI route .continueStmt
  | returnNone :
      SeqTailFullStmtReplayAtRouteCI route (.returnStmt none)
  | exprStmt
      {e : ValExpr} {τ : CppType} :
      SeqTailFullValueExprReplayAtRouteCI route e τ →
      SeqTailFullStmtReplayAtRouteCI route (.exprStmt e)
  | returnSome
      {e : ValExpr} {τ : CppType} :
      SeqTailFullValueExprReplayAtRouteCI route e τ →
      SeqTailFullStmtReplayAtRouteCI route (.returnStmt (some e))
  | declareObjNone
      {τ : CppType} {x : Ident} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      SeqTailFullStmtReplayAtRouteCI route (.declareObj τ x none)
  | declareObjSome
      {τ : CppType} {x : Ident} {e : ValExpr} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      SeqTailFullValueExprReplayAtRouteCI route e τ →
      SeqTailFullStmtReplayAtRouteCI route (.declareObj τ x (some e))
  | declareRef
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh route.Θ x →
      SeqTailAnyPlaceReplayAtRouteCI route p τ →
      SeqTailFullStmtReplayAtRouteCI route (.declareRef τ x p)
  | assign
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      SeqTailAnyPlaceReplayAtRouteCI route p τ →
      SeqTailFullValueExprReplayAtRouteCI route e τ →
      SeqTailFullStmtReplayAtRouteCI route (.assign p e)
  | seq
      {u v : CppStmt} :
      SeqTailFullStmtReplayAtRouteCI route u →
      SeqTailFullStmtReplayAtRouteCI route v →
      SeqTailFullStmtReplayAtRouteCI route (.seq u v)
  | ite
      {c : ValExpr} {u v : CppStmt} :
      SeqTailFullValueExprReplayAtRouteCI route c (.base .bool) →
      SeqTailFullStmtReplayAtRouteCI route u →
      SeqTailFullStmtReplayAtRouteCI route v →
      SeqTailFullStmtReplayAtRouteCI route (.ite c u v)
  | whileStmt
      {c : ValExpr} {body : CppStmt} :
      SeqTailFullValueExprReplayAtRouteCI route c (.base .bool) →
      SeqTailFullStmtReplayAtRouteCI route body →
      SeqTailFullStmtReplayAtRouteCI route (.whileStmt c body)
  | block
      {ss : StmtBlock} :
      SeqTailFullBlockReplayAtRouteCI route ss →
      SeqTailFullStmtReplayAtRouteCI route (.block ss)

namespace SeqTailFullStmtReplayAtRouteCI

theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {st : CppStmt}
    (h : SeqTailFullStmtReplayAtRouteCI route st) :
    StmtReadyConcrete route.Θ σ1 st := by
  induction h with
  | existing hst =>
      exact hst.ready
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
  | seq hu hv ihU ihV =>
      exact StmtReadyConcrete.seq ihU ihV
  | ite hc hu hv ihU ihV =>
      exact
        StmtReadyConcrete.ite
          hc.hasValueType
          hc.exprReady
          ihU
          ihV
  | whileStmt hc hbody ihBody =>
      exact
        StmtReadyConcrete.whileStmt
          hc.hasValueType
          hc.exprReady
          ihBody
  | block hblock =>
      exact StmtReadyConcrete.block hblock.ready

end SeqTailFullStmtReplayAtRouteCI

/-- Tail shape for full statement replay. -/
inductive SeqTailFullStmtReplayConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | ofReplay :
      SeqTailFullStmtReplayAtRouteCI route t →
      SeqTailFullStmtReplayConstructorAtRouteCI route

/-- Materialize tail readiness from full statement replay. -/
theorem seq_tail_ready_of_runtime_replay_components_full_stmt_replay_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstmt : SeqTailFullStmtReplayConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hstmt with
  | ofReplay hreplay =>
      exact hreplay.ready

/--
Assemble the runtime replay package from full statement replay.

This is the main replacement constructor for future migrations away from
`seq_tail_runtime_replay_at_route_ci_of_components`.
-/
def seq_tail_runtime_replay_at_route_ci_of_full_stmt_replay_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstmt : SeqTailFullStmtReplayConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_full_stmt_replay_at_route_ci
        hentry route components hstmt }

/-- Convenience constructor for full statement replay. -/
def seq_tail_runtime_replay_at_route_ci_of_full_stmt_replay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hstmt : SeqTailFullStmtReplayConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_full_stmt_replay_components
    hentry route components hstmt

end Cpp
