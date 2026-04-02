import CppFormalization.Cpp2.All
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

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
-/

/- =========================================
   0. 強い状態不変量と readiness 層
   ========================================= -/
/-
axiom scopesCompatible : TypeEnv → State → Prop
axiom framewiseDeclBindingCompatible : TypeEnv → State → Prop
axiom objectBindingsLiveTypedOwned : TypeEnv → State → Prop
axiom refBindingsLiveTyped : TypeEnv → State → Prop
axiom frameLocalsExact : TypeEnv → State → Prop
axiom ownedAddressesDisjoint : State → Prop
axiom heapInitializedValuesTyped : State → Prop
axiom nextIsFreshForOwnedHeap : State → Prop

/--
`TypedState` より強い runtime invariant.
核心は scope stack 対応と ownership discipline.
-/
structure ScopedTypedState (Γ : TypeEnv) (σ : State) : Prop where
  stackAligned : scopesCompatible Γ σ
  frameDeclBinding : framewiseDeclBindingCompatible Γ σ
  objectBindingsSound : objectBindingsLiveTypedOwned Γ σ
  refBindingsSound : refBindingsLiveTyped Γ σ
  localsExact : frameLocalsExact Γ σ
  ownedDisjoint : ownedAddressesDisjoint σ
  initializedValuesTyped : heapInitializedValuesTyped σ
  nextFresh : nextIsFreshForOwnedHeap σ

/--
`PlaceReady Γ σ p τ` は、`p` が現在の状態で安全に使える `τ`-place であること。
定義の中に `∃ a, BigStepPlace σ p a` を直接埋め込まない。
-/
axiom PlaceReady : TypeEnv → State → PlaceExpr → CppType → Prop

/--
`ExprReady Γ σ e τ` は、`e` が現在の状態で安全に評価できる `τ`-expr であること。
こちらも進行定理を空虚にしないため、評価可能性そのものは定義に埋め込まない。
-/
axiom ExprReady : TypeEnv → State → ValExpr → CppType → Prop

/--
statement 開始時の安全準備条件。
`ScopedTypedState` が状態側、`StmtReady` が文局所側を受け持つ。
-/
axiom StmtReady : TypeEnv → State → CppStmt → Prop
axiom BlockReady : TypeEnv → State → StmtBlock → Prop

/--
closure theorem の本当の前提。
旧 `IdealAssumptions` をそのまま使わず、必要な層を明示的に分解する。
-/
structure BodyReady (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  typed : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st
  state : ScopedTypedState Γ σ
  safe : StmtReady Γ σ st
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


/- =========================================
   5. 外部断片 interface

   ここだけを最小限の axiom にする。
   `std` 側は BodyReady を立てる責任、
   `reflection` 側は core fragment に入る責任を持つ。
   ========================================= -/
/-
structure VerifiedStdFragment where
  Name : Type
  uses : Name → Prop
  establishesBoundary : Name → TypeEnv → State → CppStmt → Prop

structure VerifiedReflectionFragment where
  Meta : Type
  generates : Meta → CppStmt → Prop

axiom std_fragment_establishes_body_ready
    {F : VerifiedStdFragment} {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesBoundary n Γ σ st →
    BodyReady Γ σ st

axiom reflection_fragment_generates_core
    {R : VerifiedReflectionFragment} {m : R.Meta} {st : CppStmt} :
    R.generates m st →
    CoreBigStepFragment st


/- =========================================
   6. 最終定理
   ========================================= -/

theorem reflective_std_function_body_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesBoundary n Γ σ st →
    R.generates m st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hboundary hgen
  have hready : BodyReady Γ σ st :=
    std_fragment_establishes_body_ready huse hboundary
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_generates_core hgen
  exact body_ready_function_body_progress_or_diverges hfrag hready

theorem reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesBoundary n Γ σ st →
    R.generates m st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hboundary hgen
  have hready : BodyReady Γ σ st :=
    std_fragment_establishes_body_ready huse hboundary
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_generates_core hgen
  exact body_ready_stmt_terminates_or_diverges hfrag hready
-/
end Cpp
