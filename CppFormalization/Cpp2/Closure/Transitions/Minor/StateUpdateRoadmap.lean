import CppFormalization.Cpp2.Closure.Foundation.StateBoundary
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
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

axiom assigns_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ScopedTypedStateConcrete Γ σ'

axiom declares_object_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ'

axiom declares_ref_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ'

axiom open_scope_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ScopedTypedStateConcrete (pushTypeScope Γ) σ'

axiom close_scope_preserves_concrete_state
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedStateConcrete Γ σ'

/- =========================================
   2. concrete から abstract theorem への橋
   ========================================= -/

axiom bodyReady_of_concrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    WellFormedStmt st →
    WellTypedFrom Γ st →
    BreakWellScoped st →
    ContinueWellScoped st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BodyReady Γ σ st

/--
この concrete 版が成り立てば、抽象版 `ScopedTypedState` に落とせるべきである。
ここは将来 theorem 化するかも。
-/
axiom scopedTypedState_of_concrete
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedState Γ σ


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

/- =========================================
   3. residual readiness
   ========================================= -/
/-
axiom seq_left_normal_preserves_body_ready_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t
-/
/-
axiom block_head_normal_preserves_block_ready_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Δ →
    BlockReadyConcrete Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ BlockReadyConcrete Δ σ' ss
-/
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

end Cpp
