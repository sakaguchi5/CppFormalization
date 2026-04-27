import CppFormalization.Cpp2.Closure.Foundation.StateBoundary
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Transitions.Assign.Preservation
import CppFormalization.Cpp2.Closure.Transitions.Scope.OpenPreservation
import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.Preservation
import CppFormalization.Cpp2.Closure.Transitions.Scope.ClosePreservation
import CppFormalization.Cpp2.Closure.Transitions.DeclareObject.Preservation
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Transitions.Minor.StateUpdateRoadmap

`reflective_std_closure_theorem` へ向かう内部主線のうち、
特に先に theorem 化すべき primitive preservation と residual readiness を固定する。

重要:
- ここでの順序は proof order でもある。
- 最初に primitive state update を固め、その後で statement-level の normal preservation に上がる。
-/

/- =========================================
   1. concrete invariant 上の primitive preservation
   ========================================= -/

theorem assigns_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hp hready hv hass
  exact assigns_preserves_scoped_typed_state_concrete hσ hp hready hv hass

theorem declares_object_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ' := by
  intro hσ hfresh hdecl
  exact declares_object_preserves_scoped_typed_state_concrete hfresh hσ hdecl

theorem declares_ref_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl
  exact declares_ref_preserves_scoped_typed_state_concrete hfresh hσ hdecl

theorem open_scope_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ScopedTypedStateConcrete (pushTypeScope Γ) σ' := by
  intro hσ hopen
  exact openScope_preserves_scoped_typed_state_concrete hσ hopen

theorem close_scope_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hclose
  exact closeScope_preserves_outer_from_pushTypeScope hσ hclose

/- =========================================
   2. concrete から abstract theorem への橋
   ========================================= -/

theorem bodyReady_of_concrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    WellFormedStmt st →
    WellTypedFrom Γ st →
    BreakWellScoped st →
    ContinueWellScoped st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BodyReady Γ σ st := by
  intro hwf htyped hbreak hcont hstate hsafe
  refine
    { wf := hwf
      typed := htyped
      breakScoped := hbreak
      continueScoped := hcont
      state := scopedTypedState_of_concrete hstate
      safe := ?_ }
  exact
    ⟨ htyped
    , noUninit_of_stmtReadyConcrete hsafe
    , noInvalidRef_of_stmtReadyConcrete hsafe ⟩

theorem assigns_preserves_scoped_typed_state_via_concrete
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ScopedTypedState Γ σ' := by
  intro hσ hp hready hv hass
  exact scopedTypedState_of_concrete
    (assigns_preserves_concrete_state hσ hp hready hv hass)

theorem declares_object_preserves_scoped_typed_state_via_concrete
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedState (declareTypeObject Γ x τ) σ' := by
  intro hσ hfresh hdecl
  exact scopedTypedState_of_concrete
    (declares_object_preserves_concrete_state hσ hfresh hdecl)

theorem declares_ref_preserves_scoped_typed_state_via_concrete
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    ScopedTypedState (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl
  exact scopedTypedState_of_concrete
    (declares_ref_preserves_concrete_state hσ hfresh hdecl)

/-
LEGACY SHELL COMMENTED OUT

理由:
- current route では residual readiness と statement-level preservation は
  `ReadinessBoundaryConcrete`, `StmtControlKernel`, `InternalClosureRoadmapConcrete/CI`
  側で扱っており、このファイル後半の高レベル roadmap axiom 群は本線ではない。
- 低レベル primitive preservation / abstract bridge は残し、
  高レベル shoulder axioms はコメント退避する。

退避対象:
- while_body_normal_preserves_body_ready_concrete
- while_body_continue_preserves_body_ready_concrete
- stmt_normal_preserves_concrete_state
- block_normal_preserves_concrete_state
- concrete_body_ready_function_body_progress_or_diverges

/- =========================================
   3. residual readiness
   ========================================= -/

axiom while_body_normal_preserves_body_ready_concrete
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body)

axiom while_body_continue_preserves_body_ready_concrete
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body)

/- =========================================
   4. statement-level normal preservation の第一到達点
   ========================================= -/

axiom stmt_normal_preserves_concrete_state
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Δ σ'

axiom block_normal_preserves_concrete_state
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ →
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    BigStepBlock σ ss .normal σ' →
    ScopedTypedStateConcrete Δ σ'

/- =========================================
   5. function-body closure の直前形
   ========================================= -/

axiom concrete_body_ready_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    WellFormedStmt st →
    WellTypedFrom Γ st →
    BreakWellScoped st →
    ContinueWellScoped st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st
-/

end Cpp
