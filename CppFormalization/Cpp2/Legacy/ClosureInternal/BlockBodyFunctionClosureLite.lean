import CppFormalization.Cpp2.Legacy.Transport.BlockBodyBoundaryTransportLite
import CppFormalization.Cpp2.Audit.Closure.Internal.InternalClosureRoadmapCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete
import CppFormalization.Cpp2.Closure.Function.FunctionBody
import CppFormalization.Cpp2.Operational.Divergence

namespace Cpp
namespace BlockBodyFunctionClosureLite

/-!
# Closure.Internal.BlockBodyFunctionClosureLite

E-lite 第4段階後半:
opened block body 自体の function-body closure を theorem 化する。

方針:
- `nil` は直ちに fallthrough。
- `cons s ss` は head statement `s` と tail block body `ss` に分ける。
- head normal のときだけ tail opened-body boundary を再構成して再帰へ渡す。
- statement-level `.block ss` へ戻す honest wrapper は次段階に残す。
-/


/-! ## local eliminator for the block-body wrapper -/

theorem BigStepFunctionBlockBody.to_block
    {σ σ' : State} {ss : StmtBlock} {ex : FunctionExit}
    (h : BigStepFunctionBlockBody σ ss ex σ') :
    match ex with
    | .fellThrough => BigStepBlock σ ss .normal σ'
    | .returned rv => BigStepBlock σ ss (.returnResult rv) σ' := by
  cases h with
  | fallthrough hblk =>
      exact hblk
  | returning hblk =>
      exact hblk


/-! ## head/tail boundary projections for canonical cons nodes -/

/-- Parent cons structural boundary から head statement structural boundary を再構成する。 -/
def cons_head_structural_of_parent
     {s : CppStmt} {ss : StmtBlock}
    (hs : BlockBodyStructuralBoundaryLite (.cons s ss)) :
    BodyStructuralBoundaryLite s := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using hs.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using hs.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using hs.continueScoped
  exact
    { wf := hwf.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/-- Parent cons structural boundary から tail block-body structural boundary を再構成する。 -/
def cons_tail_structural_of_parent
    {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
    (hs : BlockBodyStructuralBoundaryLite (.cons s ss))
    (_hN : HasTypeStmtCI .normalK Γ s Δ) :
    BlockBodyStructuralBoundaryLite ss := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using hs.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using hs.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using hs.continueScoped
  exact
    { wf := hwf.2
      breakScoped := hbreak.2
      continueScoped := hcont.2 }

/-- Parent cons dynamic boundary から head statement dynamic boundary を再構成する。 -/
def cons_head_dynamic_of_parent
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hd : BlockBodyDynamicBoundaryLite Γ σ (.cons s ss)) :
    BodyDynamicBoundary Γ σ s := by
  exact
    { state := hd.state
      safe := blockReadyConcrete_cons_head hd.safe }

/-- Canonical cons node から head adequacy を取り出す。 -/
def cons_head_adequacy_of_cons
    {Γ Δ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : BlockBodyProfileLite Δ ss}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (ha : BlockBodyAdequacyLite Γ σ (.cons hN P₁ P₂)) :
    StmtBodyAdequacyLite Γ σ P₁ := by
  cases ha with
  | cons _ hhead _ =>
      exact hhead

/-- Canonical cons node から head normal 後の tail adequacy を取り出す。 -/
def cons_tail_adequacy_of_head_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : BlockBodyProfileLite Δ ss}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (ha : BlockBodyAdequacyLite Γ σ (.cons hN P₁ P₂))
    (hstepS : BigStepStmt σ s .normal σ') :
    BlockBodyAdequacyLite Δ σ' P₂ := by
  cases ha with
  | cons _ _ htail =>
      exact htail hstepS

/-- Canonical cons node から head statement boundary を直接構成する。 -/
def cons_head_boundary_of_cons_mk
    {Γ Δ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : BlockBodyProfileLite Δ ss}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (hs : BlockBodyStructuralBoundaryLite (.cons s ss))
    (hd : BlockBodyDynamicBoundaryLite Γ σ (.cons s ss))
    (ha : BlockBodyAdequacyLite Γ σ (.cons hN P₁ P₂)) :
    BodyClosureBoundaryLite Γ σ s := by
  exact
    mkBodyClosureBoundaryLite
      (cons_head_structural_of_parent hs)
      P₁
      (cons_head_dynamic_of_parent hd)
      (cons_head_adequacy_of_cons ha)

/-- Assembled boundary 版の head projection theorem. -/
def cons_head_boundary_of_cons
    {Γ Δ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : BlockBodyProfileLite Δ ss}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (h : BlockBodyClosureBoundaryLite Γ σ (.cons s ss))
    (hprof : h.profile = .cons hN P₁ P₂) :
    BodyClosureBoundaryLite Γ σ s := by
  cases h with
  | mk hs hp hd ha =>
      cases hprof
      exact cons_head_boundary_of_cons_mk
        (hs := hs) (hd := hd) (ha := ha)

/-! ## whole opened block-body closure -/

/-- `nil` block body closes immediately with fallthrough. -/
theorem nil_block_body_function_closure_lite
    {σ : State}:
    (∃ ex σ', BigStepFunctionBlockBody σ .nil ex σ') ∨ BigStepBlockDiv σ .nil := by
  left
  refine ⟨.fellThrough, σ, ?_⟩
  exact BigStepFunctionBlockBody.fallthrough BigStepBlock.nil

/-! ## local helpers about scope depth -/

@[simp] theorem pushScope_scopes_length
    (σ : State) :
    (pushScope σ).scopes.length = σ.scopes.length + 1 := by
  simp [pushScope]

theorem declareRefState_scopes_length_of_nonempty
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hne : σ.scopes ≠ []) :
    (declareRefState σ τ x a).scopes.length = σ.scopes.length := by
  unfold declareRefState bindTopBinding
  cases hsc : σ.scopes with
  | nil =>
      contradiction
  | cons fr frs =>
      simp

theorem closeScope_scopes_length_pred
    {σ σ' : State}
    (hclose : CloseScope σ σ') :
    σ'.scopes.length + 1 = σ.scopes.length := by
  unfold CloseScope at hclose
  cases hsc : σ.scopes with
  | nil =>
      simp [popScope?, hsc] at hclose
  | cons fr frs =>
      simp [popScope?, hsc] at hclose
      subst σ'
      simp [scopes_killLocals]

private theorem nonempty_of_same_scope_length
    {σ σ' : State}
    (hlen : σ'.scopes.length = σ.scopes.length)
    (hne : σ.scopes ≠ []) :
    σ'.scopes ≠ [] := by
  cases hsc' : σ'.scopes with
  | nil =>
      simp [hsc'] at hlen
      cases hsc : σ.scopes with
      | nil =>
          contradiction
      | cons fr frs =>
          simp [hsc] at hlen
  | cons fr frs =>
      simp








end BlockBodyFunctionClosureLite
end Cpp
