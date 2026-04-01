--import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Transitions.Minor.AssignDecomposition
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareRefDecomposition
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectDecomposition

namespace Cpp

/-!
primitive 文の normal-path preservation。
ここでは `seq / ite / while / block / break / continue / return` は扱わず、
`skip / exprStmt / assign / declareObj / declareRef` のみを束ねる。
-/

def PrimitiveNormalStmt : CppStmt → Prop
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
  | .block _ => False

/- =========================================================
   1. primitive normal 文の operational bridge
   ここでは big-step の normal 実行を、すでに分解済みの
   低レベル遷移 (`Assigns`, `DeclaresObject`, `DeclaresRef`) へ落とす。
   ========================================================= -/

axiom skip_stmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State} :
    HasTypeStmtCI .normalK Γ .skip Δ →
    StmtReadyConcrete Γ σ .skip →
    BigStepStmt σ .skip .normal σ' →
    Δ = Γ ∧ σ' = σ

axiom exprStmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.exprStmt e) Δ →
    StmtReadyConcrete Γ σ (.exprStmt e) →
    BigStepStmt σ (.exprStmt e) .normal σ' →
    Δ = Γ ∧ σ' = σ

axiom assign_stmt_normal_data
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
      Assigns σ p v σ'

axiom declareObj_stmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {oe : Option ValExpr} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x oe) Δ →
    StmtReadyConcrete Γ σ (.declareObj τ x oe) →
    BigStepStmt σ (.declareObj τ x oe) .normal σ' →
    ∃ ov : Option Value,
      Δ = declareTypeObject Γ x τ ∧
      currentTypeScopeFresh Γ x ∧
      DeclaresObject σ τ x ov σ'

axiom declareRef_stmt_normal_data
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {p : PlaceExpr} :
    HasTypeStmtCI .normalK Γ (.declareRef τ x p) Δ →
    StmtReadyConcrete Γ σ (.declareRef τ x p) →
    BigStepStmt σ (.declareRef τ x p) .normal σ' →
    ∃ a,
      Δ = declareTypeRef Γ x τ ∧
      currentTypeScopeFresh Γ x ∧
      DeclaresRef σ τ x a σ'


/- =========================================================
   2. primitive normal preservation
   ========================================================= -/

theorem primitive_normal_stmt_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    PrimitiveNormalStmt st →
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep
  cases st <;> simp [PrimitiveNormalStmt] at hprim

  case skip =>
    rcases skip_stmt_normal_data hty hready hstep with ⟨hΔ, hσeq⟩
    subst hΔ
    subst hσeq
    exact hσ

  case exprStmt e =>
    rcases exprStmt_normal_data hty hready hstep with ⟨hΔ, hσeq⟩
    subst hΔ
    subst hσeq
    exact hσ

  case assign p e =>
    rcases assign_stmt_normal_data hty hready hstep with
      ⟨τ, v, hΔ, hpty, hpready, hvcompat, hassign⟩
    subst hΔ
    exact assigns_preserves_scoped_typed_state_concrete
      hσ hpty hpready hvcompat hassign

  case declareObj τ x oe =>
    rcases declareObj_stmt_normal_data hty hready hstep with
      ⟨ov, hΔ, hfresh, hdecl⟩
    subst hΔ
    exact declares_object_preserves_scoped_typed_state_concrete
      hfresh hσ hdecl

  case declareRef τ x p =>
    rcases declareRef_stmt_normal_data hty hready hstep with
      ⟨a, hΔ, hfresh, hdecl⟩
    subst hΔ
    exact declares_ref_preserves_scoped_typed_state_concrete
      hfresh hσ hdecl

theorem primitive_stmt_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    PrimitiveNormalStmt st →
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep
  exact primitive_normal_stmt_preserves_scoped_typed_state_concrete
    hprim hty hσ hready hstep

end Cpp
