import CppFormalization.Cpp2.Closure.Foundation.StateBoundary
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Internal.InternalClosureRoadmap

external fragment interface を使う前に、core semantics 内部で成立すべき theorem 群。

ここでは evaluator adequacy は扱わない。
closure 主線に必要な progress / preservation / no-stuck のみを置く。
-/

/- =========================================
   1. place / expr の進行
   ========================================= -/

axiom place_ready_progress
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    ScopedTypedState Γ σ →
    HasPlaceType Γ p τ →
    PlaceReady Γ σ p τ →
    ∃ a, BigStepPlace σ p a

axiom expr_ready_progress
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ScopedTypedState Γ σ →
    HasValueType Γ e τ →
    ExprReady Γ σ e τ →
    ∃ v, BigStepValue σ e v

/- =========================================
   2. 原始操作の preservation
   ========================================= -/

axiom assigns_preserves_scoped_typed_state
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} {τ : CppType} :
    ScopedTypedState Γ σ →
    HasPlaceType Γ p τ →
    PlaceReady Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ScopedTypedState Γ σ'

axiom declares_object_preserves_scoped_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ScopedTypedState Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedState (declareTypeObject Γ x τ) σ'

axiom declares_ref_preserves_scoped_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    ScopedTypedState Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    ScopedTypedState (declareTypeRef Γ x τ) σ'

axiom open_scope_preserves_scoped_typed_state
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedState Γ σ →
    OpenScope σ σ' →
    ScopedTypedState (pushTypeScope Γ) σ'

axiom close_scope_preserves_scoped_typed_state
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedState (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedState Γ σ'

/- =========================================
   3. normal-path の statement / block preservation
   ========================================= -/

axiom stmt_normal_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedState Γ σ →
    StmtReady Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedState Δ σ'

axiom block_normal_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ →
    ScopedTypedState Γ σ →
    BlockReady Γ σ ss →
    BigStepBlock σ ss .normal σ' →
    ScopedTypedState Δ σ'

axiom seq_left_normal_preserves_body_ready
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    BodyReady Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    BodyReady Δ σ' t

axiom block_head_normal_preserves_block_ready
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Δ →
    BlockReady Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    BlockReady Δ σ' ss

axiom while_body_normal_preserves_body_ready
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    BodyReady Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    BodyReady Γ σ' (.whileStmt c body)

axiom while_body_continue_preserves_body_ready
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    BodyReady Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    BodyReady Γ σ' (.whileStmt c body)

/- =========================================
   4. 内部主定理
   ========================================= -/

axiom body_ready_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReady Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/--
raw statement 版は function-body 版から落とす系にする。
closure の主役はあくまで function-body 側。
-/
theorem body_ready_stmt_terminates_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReady Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  rcases body_ready_function_body_progress_or_diverges (Γ := Γ) (σ := σ) (st := st) hfrag hready with hbody | hdiv
  · left
    rcases hbody with ⟨ex, σ', hfb⟩
    cases ex with
    | fellThrough =>
        refine ⟨.normal, σ', ?_⟩
        simpa using (BigStepFunctionBody.to_stmt hfb)
    | returned rv =>
        refine ⟨.returnResult rv, σ', ?_⟩
        simpa using (BigStepFunctionBody.to_stmt hfb)
  · exact Or.inr hdiv

end Cpp
