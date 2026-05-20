import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Stmt

namespace Cpp

/-!
# Seq tail replay: structured statement replay
-/

/- =========================================================
   Stage 3j: theorem-backed materialization for while/block tails
   ========================================================= -/

/--
Block-local replay for the selected tail route.

Blocks are checked under pushed type/runtime scopes, so this is deliberately
separate from `SeqTailStmtReplayAtRouteCI`, which replays statements directly at
`(route.Θ, σ1)`.
-/
inductive SeqTailBlockReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    StmtBlock → Prop where
  | nil :
      SeqTailBlockReplayAtRouteCI route .nil
  | cons
      {st : CppStmt} {ss : StmtBlock} :
      StmtReadyConcrete (pushTypeScope route.Θ) (pushScope σ1) st →
      SeqTailBlockReplayAtRouteCI route ss →
      SeqTailBlockReplayAtRouteCI route (.cons st ss)

namespace SeqTailBlockReplayAtRouteCI

/-- Block-local replay materializes block readiness in the pushed block scope. -/
theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {ss : StmtBlock}
    (h : SeqTailBlockReplayAtRouteCI route ss) :
    BlockReadyConcrete (pushTypeScope route.Θ) (pushScope σ1) ss := by
  induction h with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hst hss ih =>
      exact BlockReadyConcrete.cons hst ih

end SeqTailBlockReplayAtRouteCI

/--
Structured-statement tail shapes whose readiness is constructor-backed.

This stage covers `while` and `block`.
-/
inductive SeqTailStructuredStmtConstructorAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  | whileStmt
      {c : ValExpr} {body : CppStmt} :
      SeqTailValueExprReplayAtRouteCI route c (.base .bool) →
      SeqTailStmtReplayAtRouteCI route body →
      t = .whileStmt c body →
      SeqTailStructuredStmtConstructorAtRouteCI route
  | block
      {ss : StmtBlock} :
      SeqTailBlockReplayAtRouteCI route ss →
      t = .block ss →
      SeqTailStructuredStmtConstructorAtRouteCI route

/--
Materialize tail readiness for structured statement tails.

This is theorem-backed and does not use the broad materialization axiom.
-/
theorem seq_tail_ready_of_runtime_replay_components_structured_stmt_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstructured : SeqTailStructuredStmtConstructorAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t := by
  cases hstructured with
  | whileStmt hc hbody hshape =>
      cases hshape
      exact
        StmtReadyConcrete.whileStmt
          hc.hasValueType
          hc.exprReady
          hbody.ready
  | block hblock hshape =>
      cases hshape
      exact StmtReadyConcrete.block hblock.ready

/--
Assemble the runtime replay package for a structured statement tail using the
theorem-backed readiness fragment.

Unlike `seq_tail_runtime_replay_at_route_ci_of_components`, this definition does
not use the broad materialization axiom.
-/
def seq_tail_runtime_replay_at_route_ci_of_structured_stmt_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route)
    (hstructured : SeqTailStructuredStmtConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_structured_stmt_at_route_ci
        hentry route components hstructured }

/--
Convenience constructor for structured statement replay using the current coarse
component witnesses.
-/
def seq_tail_runtime_replay_at_route_ci_of_structured_stmt
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (hstructured : SeqTailStructuredStmtConstructorAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  let components : SeqTailRuntimeReplayComponentsAtRouteCI route :=
    { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
      derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
      loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial }
  seq_tail_runtime_replay_at_route_ci_of_structured_stmt_components
    hentry route components hstructured

end Cpp
