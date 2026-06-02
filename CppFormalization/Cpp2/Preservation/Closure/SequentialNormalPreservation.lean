import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Static.Typing.ControlIndexed
import CppFormalization.Cpp2.Metatheory.Closure.Unclassified.ReadinessResidualBoundary
import CppFormalization.Cpp2.Preservation.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Continuation.Boundary.Seq

namespace Cpp

/-!
`seq` で本質なのは、左の normal 実行のあとに「右 `t` が post-state / post-env
のもとで実行境界を持つ」こと、すなわち residual boundary の再構成である。

このファイルでは:
- `HasTypeStmtCI .normalK Γ (.seq s t) Δ` の分解
- `StmtReadyConcrete Γ σ (.seq s t)` から左 ready を取り出すこと
- 左 normal 実行後の residual boundary を、左 preservation と tail continuation
  を引数にして再構成する一般形
- primitive-left case をその一般形の系として回収すること
- downstream でよく使う「左の post-env が既に決まっている場合」の
  ready/state 境界を別 theorem として薄く切り出すこと
を整理する。

重要:
- low-level exact tail-ready kernel / `削除済みaxiom` には
  もう給電しない。
- current mainline が public に使うべき主語は `StmtReadyConcrete Θ σ' t`
  単体ではなく、post-route の `StmtContinuationDynamicBoundary Θ σ' t`、
  あるいはそれを詰めた `SeqResidualBoundary Δ σ' t` である。
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
Low-level residual-ready projection from an explicit tail continuation boundary.

This is no longer a transport theorem.  Tail readiness is obtained by projecting
from the post-route continuation boundary.
-/
theorem seq_ready_right_after_left_normal_of_tail_continuation
    {Θ : TypeEnv} {σ' : State} {t : CppStmt}
    (tail : StmtContinuationDynamicBoundary Θ σ' t) :
    StmtReadyConcrete Θ σ' t :=
  tail.safe


/- =========================================================
   2. residual boundary の主定理
   ========================================================= -/

/--
Generic residual-boundary reconstruction after a left normal step.

The two abstract inputs are separated:

* `hpres` proves the post-state invariant for the intermediate environment `Θ`;
* `htail` proves that the selected post-route tail continuation exists.

Thus the theorem no longer manufactures tail readiness by exact-tail transport.
-/
theorem seq_left_normal_preserves_residual_boundary_of_left_preservation
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (hpres :
      ∀ {Θ : TypeEnv},
        HasTypeStmtCI .normalK Γ s Θ →
        ScopedTypedStateConcrete Γ σ →
        StmtReadyConcrete Γ σ s →
        BigStepStmt σ s .normal σ' →
        ScopedTypedStateConcrete Θ σ')
    (htail :
      ∀ {Θ : TypeEnv},
        HasTypeStmtCI .normalK Γ s Θ →
        HasTypeStmtCI .normalK Θ t Δ →
        ScopedTypedStateConcrete Θ σ' →
        StmtReadyConcrete Γ σ (.seq s t) →
        BigStepStmt σ s .normal σ' →
        StmtContinuationDynamicBoundary Θ σ' t) :
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
  have htailDyn : StmtContinuationDynamicBoundary Θ σ' t :=
    htail htyLeft htyRight hσ' hreadySeq hstepLeft
  exact ⟨Θ, htyRight, htailDyn.state, htailDyn.safe⟩


/- =========================================================
   3. left-typed post boundary の一般定理
   ========================================================= -/

/--
When the post-environment of the left statement is already fixed as `Δ`, we can
reconstruct the concrete state/ready pair for the right statement without
mentioning the final codomain of the whole `seq`.

The right-tail readiness is projected from an explicit post-route tail
continuation boundary.
-/
theorem seq_left_normal_preserves_ready_of_left_preservation
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (hpres :
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Δ σ')
    (htail :
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Δ σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtContinuationDynamicBoundary Δ σ' t) :
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
  have htailDyn : StmtContinuationDynamicBoundary Δ σ' t :=
    htail htyLeft hσ' hreadySeq hstepLeft
  exact ⟨htailDyn.state, htailDyn.safe⟩


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
    (∀ {Θ : TypeEnv},
      HasTypeStmtCI .normalK Γ s Θ →
      HasTypeStmtCI .normalK Θ t Δ →
      ScopedTypedStateConcrete Θ σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtContinuationDynamicBoundary Θ σ' t) →
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro hprim htail htySeq hσ hreadySeq hstepLeft
  exact
    seq_left_normal_preserves_residual_boundary_of_left_preservation
      (s := s) (t := t) (Γ := Γ) (Δ := Δ) (σ := σ) (σ' := σ')
      (hpres := by
        intro Θ htyLeft hσ0 hreadyLeft hstepLeft0
        exact
          primitive_stmt_normal_preserves_scoped_typed_state_concrete
            hprim htyLeft hσ0 hreadyLeft hstepLeft0)
      (htail := htail)
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
    (∀ {Θ' : TypeEnv},
      HasTypeStmtCI .normalK Γ s Θ' →
      HasTypeStmtCI .normalK Θ' t Δ →
      ScopedTypedStateConcrete Θ' σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtContinuationDynamicBoundary Θ' σ' t) →
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    HasTypeStmtCI .normalK Θ t Δ →
    (∀ {Θ'}, HasTypeStmtCI .normalK Θ' t Δ → Θ' = Θ) →
    ScopedTypedStateConcrete Θ σ' := by
  intro hprim htail htySeq hσ hreadySeq hstepLeft htyRight huniq
  rcases primitive_left_seq_normal_preserves_residual_boundary
      hprim htail htySeq hσ hreadySeq hstepLeft with
    ⟨Θ', htyRight', hσ', _hreadyRight'⟩
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
    (∀ {Θ' : TypeEnv},
      HasTypeStmtCI .normalK Γ s Θ' →
      HasTypeStmtCI .normalK Θ' t Δ →
      ScopedTypedStateConcrete Θ' σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtContinuationDynamicBoundary Θ' σ' t) →
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    HasTypeStmtCI .normalK Θ t Δ →
    (∀ {Θ'}, HasTypeStmtCI .normalK Θ' t Δ → Θ' = Θ) →
    StmtReadyConcrete Θ σ' t := by
  intro hprim htail htySeq hσ hreadySeq hstepLeft htyRight huniq
  rcases primitive_left_seq_normal_preserves_residual_boundary
      hprim htail htySeq hσ hreadySeq hstepLeft with
    ⟨Θ', htyRight', _hσ', hreadyRight'⟩
  have hEq : Θ' = Θ := by
    exact huniq htyRight'
  subst hEq
  exact hreadyRight'

end Cpp
