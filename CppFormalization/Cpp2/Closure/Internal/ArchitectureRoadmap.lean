import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.CoreBigStepFragment
import CppFormalization.Cpp2.Closure.Foundation.StateBoundary
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.ArchitectureRoadmap

`reflective_std_closure_theorem` までの数学的な主線だけを取り出した
再設計用ロードマップ。

意図:
- 旧 `Axioms.lean` のように、保存・安全・評価器・bridge 契約を一枚に混ぜない。
- 内部 closure の本線では、`IdealAssumptions` を直接使わず、
  より強く分解された `ScopedTypedState` / `BodyReady` を使う。
- `break` / `continue` の top-level 排除は既存の theorem をそのまま使う。
- evaluator adequacy や failure semantics は別ファイルへ分離し、このファイルには入れない。

このファイルは「今後 theorem にしていくべき命題」を、
数理的に適切な粒度で宣言し直したもの。
未証明部分は `axiom` として置いているが、
final theorem 自体はそれらをどう接続するかが見える形で書く。

Import policy:
- do not import `Cpp2.All` here.
- this roadmap is itself imported by the full aggregate, so importing `Cpp2.All`
  would create an aggregate cycle.
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

   旧 `bigstep_preserves_typed_state` は all-control 版だと偽なので捨てる。
   正しいのは `.normal` 限定保存と、残余文 readiness の保存。
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

   ここで初めて no-stuck / closure の本体を置く。
   evaluator adequacy はこの主線から分離する。
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
