import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.ReadinessResidualBoundary
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
`seq` で本質なのは、左の normal 実行のあとに「右 `t` が post-state / post-env
のもとで実行境界を持つ」こと、すなわち residual boundary の再構成である。

このファイルでは:
- `HasTypeStmtCI .normalK Γ (.seq s t) Δ` の分解
- `StmtReadyConcrete Γ σ (.seq s t)` から左 ready を取り出すこと
- 左 normal 実行後の residual boundary を、左 preservation を引数にして
  再構成する一般形
- primitive-left case をその一般形の系として回収すること
- downstream でよく使う「左の post-env が既に決まっている場合」の
  ready/state 境界を別 theorem として薄く切り出すこと
を整理する。

重要:
- `seq_ready_right_after_left_normal` は low-level な residual-ready kernel のまま残す。
- current mainline が public に使うべき主語は `StmtReadyConcrete Θ σ' t` 単体ではなく、
  `SeqResidualBoundary Δ σ' t` である。
- ただし downstream の concrete roadmap では、「最終 codomain ではなく
  左の post-env `Δ` だけを使って右 ready を得たい」局面もある。
  そのための中間 theorem もここで明示化する。
-/

/- =========================================================
   1. seq の typing / readiness 分解
   ========================================================= -/

theorem seq_typing_data
    {Γ Δ : TypeEnv} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ∃ Θ,
      HasTypeStmtCI .normalK Γ s Θ ∧
      HasTypeStmtCI .normalK Θ t Δ := by
  intro h
  cases h with
  | seq_normal hs ht =>
      exact ⟨_, hs, ht⟩

theorem seq_ready_left
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.seq s t) →
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | seq hs _ =>
      exact hs

/--
Low-level residual-ready projection kernel.

This is intentionally narrower than the public residual-boundary theorem:
it only says that once a post-environment `Θ` and a post-state proof are already
available, right-side readiness can be reconstructed.
-/
axiom seq_ready_right_after_left_normal
    {Γ Θ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Θ →
    ScopedTypedStateConcrete Θ σ' →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    StmtReadyConcrete Θ σ' t


/- =========================================================
   2. residual boundary の主定理
   ========================================================= -/

/--
Generic residual-boundary reconstruction after a left normal step.

The only abstract input is a left-preservation callback producing the concrete
post-state invariant for the intermediate environment `Θ`.
-/
theorem seq_left_normal_preserves_residual_boundary_of_left_preservation
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (hpres :
      ∀ {Θ : TypeEnv},
        HasTypeStmtCI .normalK Γ s Θ →
        ScopedTypedStateConcrete Γ σ →
        StmtReadyConcrete Γ σ s →
        BigStepStmt σ s .normal σ' →
        ScopedTypedStateConcrete Θ σ') :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro htySeq hσ hreadySeq hstepLeft
  rcases seq_typing_data htySeq with ⟨Θ, htyLeft, htyRight⟩
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hreadySeq
  have hσ' : ScopedTypedStateConcrete Θ σ' :=
    hpres htyLeft hσ hreadyLeft hstepLeft
  have hreadyRight : StmtReadyConcrete Θ σ' t :=
    seq_ready_right_after_left_normal htyLeft hσ' hreadySeq hstepLeft
  exact ⟨Θ, htyRight, hσ', hreadyRight⟩


/- =========================================================
   3. left-typed post boundary の一般定理
   ========================================================= -/

/--
When the post-environment of the left statement is already fixed as `Δ`,
we can reconstruct the concrete state/ready pair for the right statement
without mentioning the final codomain of the whole `seq`.

This is the right abstraction for downstream concrete roadmap lemmas.
-/
theorem seq_left_normal_preserves_ready_of_left_preservation
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (hpres :
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Δ σ') :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t := by
  intro htyLeft hreadySeq hstepLeft hσ
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hreadySeq
  have hσ' : ScopedTypedStateConcrete Δ σ' :=
    hpres htyLeft hσ hreadyLeft hstepLeft
  have hreadyRight : StmtReadyConcrete Δ σ' t :=
    seq_ready_right_after_left_normal htyLeft hσ' hreadySeq hstepLeft
  exact ⟨hσ', hreadyRight⟩


/- =========================================================
   4. primitive-left corollaries
   ========================================================= -/

theorem primitive_left_seq_normal_preserves_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    (match s with
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
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro hprim htySeq hσ hreadySeq hstepLeft
  exact
    seq_left_normal_preserves_residual_boundary_of_left_preservation
      (s := s) (t := t) (Γ := Γ) (Δ := Δ) (σ := σ) (σ' := σ')
      (hpres := by
        intro Θ htyLeft hσ0 hreadyLeft hstepLeft0
        exact
          primitive_stmt_normal_preserves_scoped_typed_state_concrete
            hprim htyLeft hσ0 hreadyLeft hstepLeft0)
      htySeq hσ hreadySeq hstepLeft

theorem primitive_left_seq_normal_preserves_right_state
    {Γ Δ Θ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    (match s with
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
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    HasTypeStmtCI .normalK Θ t Δ →
    (∀ {Θ'}, HasTypeStmtCI .normalK Θ' t Δ → Θ' = Θ) →
    ScopedTypedStateConcrete Θ σ' := by
  intro hprim htySeq hσ hreadySeq hstepLeft htyRight huniq
  rcases primitive_left_seq_normal_preserves_residual_boundary
      hprim htySeq hσ hreadySeq hstepLeft with
    ⟨Θ', htyRight', hσ', hreadyRight'⟩
  have hEq : Θ' = Θ := by
    exact huniq htyRight'
  subst hEq
  exact hσ'

theorem primitive_left_seq_normal_preserves_right_ready
    {Γ Δ Θ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    (match s with
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
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    HasTypeStmtCI .normalK Θ t Δ →
    (∀ {Θ'}, HasTypeStmtCI .normalK Θ' t Δ → Θ' = Θ) →
    StmtReadyConcrete Θ σ' t := by
  intro hprim htySeq hσ hreadySeq hstepLeft htyRight huniq
  rcases primitive_left_seq_normal_preserves_residual_boundary
      hprim htySeq hσ hreadySeq hstepLeft with
    ⟨Θ', htyRight', hσ', hreadyRight'⟩
  have hEq : Θ' = Θ := by
    exact huniq htyRight'
  subst hEq
  exact hreadyRight'

end Cpp
