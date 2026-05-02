import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryLite
import CppFormalization.Cpp2.Closure.Foundation.ReadinessInversions
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapCI

namespace Cpp
namespace SeqBoundaryTransportLite

/-!
# Closure.Internal.Transport.SeqBoundaryTransportLite

E-lite 補正後の `seq` transport theorem 群。

方針:
- parent lite boundary から left normal 実行後の tail lite boundary を再構成する。
- old coarse typing へは降りない。
- readiness inversion は foundation 側へ分離し、このファイルでは client として使う。
- profile canonicality はまだ型に埋め込まれていないので、assembled theorem では
  canonical seq-node 仮定を明示する。
-/

/-! ## structural transport -/

/-- Parent seq structural boundary から tail lite structural boundary を再構成する。 -/
theorem seq_tail_structural_of_parent
    {s t : CppStmt}
    (hs : BodyStructuralBoundaryLite (.seq s t)) :
    BodyStructuralBoundaryLite t := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hs.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped, BreakWellScopedAt] using hs.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped, ContinueWellScopedAt] using hs.continueScoped
  exact
    { wf := hwf.2
      breakScoped := hbreak.2
      continueScoped := hcont.2 }

/-! ## dynamic transport -/

/-- Left normal 実行で seq tail の dynamic boundary を再構成する。 -/
theorem seq_tail_dynamic_of_left_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (hd : BodyDynamicBoundary Γ σ (.seq s t))
    (hN : HasTypeStmtCI .normalK Γ s Δ)
    (hstepS : BigStepStmt σ s .normal σ')
    (hpresS :
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Δ σ') :
    BodyDynamicBoundary Δ σ' t := by
  have hreadyS : StmtReadyConcrete Γ σ s :=
    seq_ready_left hd.safe

  have hstate' : ScopedTypedStateConcrete Δ σ' :=
    hpresS hd.state hreadyS hstepS

  have hreadyTail : StmtReadyConcrete Δ σ' t :=
    seq_ready_right_after_left_normal
      hN
      hstate'
      hd.safe
      hstepS

  exact
    BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
      hstate'
      hreadyTail

/-! ## adequacy projection -/

/-- Canonical seq node から left adequacy を取り出す。 -/
def seq_left_adequacy_of_seq
    {Γ Δ : TypeEnv} {σ : State} {s t : CppStmt}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : StmtBodyProfileLite Δ t}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (ha : StmtBodyAdequacyLite Γ σ (.seq hN P₁ P₂)) :
    StmtBodyAdequacyLite Γ σ P₁ := by
  cases ha with
  | seq _ hleft _ =>
      exact hleft

/-- Canonical seq node から left normal 実行後の tail adequacy を取り出す。 -/
def seq_tail_adequacy_of_left_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : StmtBodyProfileLite Δ t}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (ha : StmtBodyAdequacyLite Γ σ (.seq hN P₁ P₂))
    (hstepS : BigStepStmt σ s .normal σ') :
    StmtBodyAdequacyLite Δ σ' P₂ := by
  cases ha with
  | seq _ _ htail =>
      exact htail hstepS

/-! ## assembled tail boundary -/

/-- Canonical seq node を直接受け取る tail boundary constructor. -/
def seq_tail_boundary_of_left_normal_mk
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : StmtBodyProfileLite Δ t}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (hs : BodyStructuralBoundaryLite (.seq s t))
    (hd : BodyDynamicBoundary Γ σ (.seq s t))
    (ha : StmtBodyAdequacyLite Γ σ (.seq hN P₁ P₂))
    (hstepS : BigStepStmt σ s .normal σ')
    (hpresS :
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Δ σ') :
    BodyClosureBoundaryLite Δ σ' t := by
  exact
    mkBodyClosureBoundaryLite
      (seq_tail_structural_of_parent hs)
      P₂
      (seq_tail_dynamic_of_left_normal hd hN hstepS hpresS)
      (seq_tail_adequacy_of_left_normal ha hstepS)

/-- Assembled boundary 版の seq tail transport theorem. -/
def seq_tail_boundary_of_left_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : StmtBodyProfileLite Δ t}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (h : BodyClosureBoundaryLite Γ σ (.seq s t))
    (hprof : h.profile = .seq hN P₁ P₂)
    (hstepS : BigStepStmt σ s .normal σ')
    (hpresS :
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Δ σ') :
    BodyClosureBoundaryLite Δ σ' t := by
  cases h with
  | mk hs hp hd ha =>
      cases hprof
      exact seq_tail_boundary_of_left_normal_mk
        (hs := hs) (hd := hd) (ha := ha) hstepS hpresS

end SeqBoundaryTransportLite
end Cpp
