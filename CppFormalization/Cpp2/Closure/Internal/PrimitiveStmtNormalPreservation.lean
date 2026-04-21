import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Transitions.Minor.AssignDecomposition
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareRefDecomposition
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectDecomposition
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel
import CppFormalization.Cpp2.Lemmas.ExprTypeUniqueness

namespace Cpp

/-!
primitive 文の normal-path preservation。
ここでは `seq / ite / while / block / break / continue / return` は扱わず、
`skip / exprStmt / assign / declareObj / declareRef` のみを束ねる。

重要:
- 以前の `PrimitiveNormalStmt` は削除した。
- ただしこのファイルの定理自体は依然として「primitive case 専用」である。
- したがって aggregate theorem には、外部定義ではなく inline な構文制約を置く。
- declareRef は namesExact を含む本線 invariant の上で、weak ではなく
  decomposition theorem へ直接落とす。
-/

/- =========================================================
   1. primitive normal 文の operational bridge
   ========================================================= -/

theorem skip_stmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State} :
    HasTypeStmtCI .normalK Γ .skip Δ →
    StmtReadyConcrete Γ σ .skip →
    BigStepStmt σ .skip .normal σ' →
    Δ = Γ ∧ σ' = σ := by
  intro hty hready hstep
  cases hty
  cases hready
  cases hstep
  exact ⟨rfl, rfl⟩

theorem exprStmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.exprStmt e) Δ →
    StmtReadyConcrete Γ σ (.exprStmt e) →
    BigStepStmt σ (.exprStmt e) .normal σ' →
    Δ = Γ ∧ σ' = σ := by
  intro hty hready hstep
  cases hty
  cases hready
  cases hstep
  exact ⟨rfl, rfl⟩

theorem assign_stmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.assign p e) Δ →
    StmtReadyConcrete Γ σ (.assign p e) →
    BigStepStmt σ (.assign p e) .normal σ' →
    ∃ τ v,
      Δ = Γ ∧
      HasPlaceType Γ p τ ∧
      PlaceReadyConcrete Γ σ p τ ∧
      ValueCompat v τ ∧
      Assigns σ p v σ' := by
  intro hty hready hstep
  -- 1. hty から静的な型情報を出す
  cases hty with
  | assign hpty hvty =>
      -- 2. hready から動的な（実行時の）型情報を取り出す
      cases hready with
      | assign hpty_rd hpready hvty_rd heready =>
          -- ここで hpty_rd と hpty の型が同じであることを証明し、subst で同期させる
          have heq := hasPlaceType_unique hpty hpty_rd
          subst heq
          -- 3. hstep から値と実行の証拠を取り出す
          cases hstep with
          | assign h_bs_val h_assigns =>
              -- 型変数 τ✝ に名前を付けておくと確実です
              rename_i τ_val v_val
              -- ∃ τ v なので、τ に τ_val を、v に v_val を指定
              exists τ_val, v_val
              -- ⟨Δ=Γ, HasPlaceType, PlaceReady, ValueCompat, Assigns⟩
              exact ⟨rfl, hpty, hpready, expr_ready_eval_compat heready h_bs_val, h_assigns⟩

theorem declareObj_stmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {oe : Option ValExpr} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x oe) Δ →
    StmtReadyConcrete Γ σ (.declareObj τ x oe) →
    BigStepStmt σ (.declareObj τ x oe) .normal σ' →
    ∃ ov : Option Value,
      Δ = declareTypeObject Γ x τ ∧
      currentTypeScopeFresh Γ x ∧
      DeclaresObject σ τ x ov σ' := by
  intro hty hready hstep
  cases hty with
  | declareObjNone hfresh hobj =>
      cases hready with
      | declareObjNone _ _ =>
          cases hstep with
          | declareObjNone hdecl =>
              exact ⟨none, rfl, hfresh, hdecl⟩
  | declareObjSome hfresh hobj hvty =>
      cases hready with
      | declareObjSome _ _ _ hre =>
          cases hstep with
          | declareObjSome h_bs_val hdecl =>
              rename_i v_val
              exists (some v_val)

theorem declareRef_stmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {p : PlaceExpr} :
    HasTypeStmtCI .normalK Γ (.declareRef τ x p) Δ →
    StmtReadyConcrete Γ σ (.declareRef τ x p) →
    BigStepStmt σ (.declareRef τ x p) .normal σ' →
    ∃ a,
      Δ = declareTypeRef Γ x τ ∧
      currentTypeScopeFresh Γ x ∧
      HasPlaceType Γ p τ ∧
      PlaceReadyConcrete Γ σ p τ ∧
      DeclaresRef σ τ x a σ' := by
  intro hty hready hstep
  cases hty with
  | declareRef hfresh hpty =>
      cases hready with
      | declareRef _ hpty_rd hpready =>  -- hpty_rd を取り出しておくと型安全
          cases hstep with
          | declareRef h_bs_p hdecl =>
              -- BigStepPlace のインデックスに隠れているアドレス a を a_val として拾う
              rename_i a_val
              exists a_val

/- =========================================================
   2. constructor ごとの preservation
   ========================================================= -/

theorem skip_stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} :
    HasTypeStmtCI .normalK Γ .skip Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ .skip →
    BigStepStmt σ .skip .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep
  rcases skip_stmt_normal_data hty hready hstep with ⟨hΔ, hσeq⟩
  subst hΔ
  subst hσeq
  exact hσ

theorem exprStmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.exprStmt e) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.exprStmt e) →
    BigStepStmt σ (.exprStmt e) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep
  rcases exprStmt_normal_data hty hready hstep with ⟨hΔ, hσeq⟩
  subst hΔ
  subst hσeq
  exact hσ

theorem assign_stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.assign p e) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.assign p e) →
    BigStepStmt σ (.assign p e) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep
  rcases assign_stmt_normal_data hty hready hstep with
    ⟨τ, v, hΔ, hpty, hpready, hvcompat, hassign⟩
  subst hΔ
  exact assigns_preserves_scoped_typed_state_concrete
    hσ hpty hpready hvcompat hassign

theorem declareObj_stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {oe : Option ValExpr} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x oe) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.declareObj τ x oe) →
    BigStepStmt σ (.declareObj τ x oe) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep
  rcases declareObj_stmt_normal_data hty hready hstep with
    ⟨ov, hΔ, hfresh, hdecl⟩
  subst hΔ
  exact declares_object_preserves_scoped_typed_state_concrete
    hfresh hσ hdecl

theorem declareRef_stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {p : PlaceExpr} :
    HasTypeStmtCI .normalK Γ (.declareRef τ x p) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.declareRef τ x p) →
    BigStepStmt σ (.declareRef τ x p) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep
  rcases declareRef_stmt_normal_data hty hready hstep with
    ⟨a, hΔ, hfresh, hpty, hpready, hdecl⟩
  subst hΔ
  exact declares_ref_preserves_scoped_typed_state_concrete
    hfresh hσ hdecl

/- =========================================================
   3. aggregate theorem for primitive constructors only
   ========================================================= -/

theorem primitive_normal_stmt_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    (match st with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) →
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep
  cases st <;> simp at hprim
  case skip =>
    exact skip_stmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep
  case exprStmt e =>
    exact exprStmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep
  case assign p e =>
    exact assign_stmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep
  case declareObj τ x oe =>
    exact declareObj_stmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep
  case declareRef τ x p =>
    exact declareRef_stmt_normal_preserves_scoped_typed_state_concrete
      hty hσ hready hstep

theorem primitive_stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    (match st with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) →
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep
  exact primitive_normal_stmt_preserves_scoped_typed_state_concrete
    hprim hty hσ hready hstep

theorem assign_stmt_normal_write_effect
    {Γ Δ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.assign p e) Δ →
    StmtReadyConcrete Γ σ (.assign p e) →
    BigStepStmt σ (.assign p e) .normal σ' →
    ∃ τ v,
      Δ = Γ ∧
      HasPlaceType Γ p τ ∧
      PlaceReadyConcrete Γ σ p τ ∧
      HasValueType Γ e τ ∧
      ValueCompat v τ ∧
      AssignWriteEffect σ σ' p v := by
  intro hty hready hstep
  cases hty with
  | assign hpty hvty =>
      rcases assign_stmt_normal_data
          (HasTypeStmtCI.assign hpty hvty) hready hstep with
        ⟨τ, v, hΔ, hpty', hpready, hvcompat, hassign⟩
      have hτ : τ = _ := hasPlaceType_unique hpty' hpty
      subst hτ
      exact
        ⟨_, v, hΔ, hpty, hpready, hvty, hvcompat,
          assignWriteEffect_of_Assigns hassign⟩

end Cpp
