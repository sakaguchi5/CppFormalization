import CppFormalization.Cpp2.Closure.Internal.Transport.SeqBoundaryTransportLite
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp
namespace SeqFunctionBodyClosureLite

/-!
# Closure.Internal.SeqFunctionBodyClosureLite

E-lite 第3段階:
- canonical seq-node lite boundary から left lite boundary を再構成する。
- left closure と tail closure をつないで、whole `seq` の function-body closure を与える。

方針:
- left normal の場合だけ `SeqBoundaryTransportLite.seq_tail_boundary_of_left_normal`
  を使って tail lite boundary を再構成する。
- left return は `BigStepStmt.seqReturn` で whole seq return へ持ち上げる。
- left divergence は `BigStepStmtDiv.seqLeft`、tail divergence は
  `BigStepStmtDiv.seqRight` で whole seq divergence へ持ち上げる。

重要:
- まだ `StmtBodyProfileLite` 自体は arbitrary `leaf` を許すため、
  assembled theorem は canonical seq-node 仮定 `h.profile = .seq hN P₁ P₂`
  を明示的に要求する。
-/


/-! ## left boundary projection -/

/-- Parent seq structural boundary から left lite structural boundary を再構成する。 -/
def seq_left_structural_of_parent
    {s t : CppStmt}
    (hs : BodyStructuralBoundaryLite (.seq s t)) :
    BodyStructuralBoundaryLite s := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hs.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped, BreakWellScopedAt] using hs.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped, ContinueWellScopedAt] using hs.continueScoped
  exact
    { wf := hwf.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/-- Parent seq dynamic boundary から left dynamic boundary を再構成する。 -/
def seq_left_dynamic_of_parent
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hd : BodyDynamicBoundary Γ σ (.seq s t)) :
    BodyDynamicBoundary Γ σ s := by
  exact
    { state := hd.state
      safe := stmtReadyConcrete_seq_left hd.safe }

/-- Canonical seq node から left lite boundary を直接構成する。 -/
def seq_left_boundary_of_seq_mk
    {Γ Δ : TypeEnv} {σ : State} {s t : CppStmt}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : StmtBodyProfileLite Δ t}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (hs : BodyStructuralBoundaryLite (.seq s t))
    (hd : BodyDynamicBoundary Γ σ (.seq s t))
    (ha : StmtBodyAdequacyLite Γ σ (.seq hN P₁ P₂)) :
    BodyClosureBoundaryLite Γ σ s := by
  exact
    mkBodyClosureBoundaryLite
      (seq_left_structural_of_parent hs)
      P₁
      (seq_left_dynamic_of_parent hd)
      (SeqBoundaryTransportLite.seq_left_adequacy_of_seq ha)

/-- Assembled boundary 版の left projection theorem. -/
def seq_left_boundary_of_seq
    {Γ Δ : TypeEnv} {σ : State} {s t : CppStmt}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : StmtBodyProfileLite Δ t}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (h : BodyClosureBoundaryLite Γ σ (.seq s t))
    (hprof : h.profile = .seq hN P₁ P₂) :
    BodyClosureBoundaryLite Γ σ s := by
  cases h with
  | mk hs hp hd ha =>
      cases hprof
      exact seq_left_boundary_of_seq_mk
        (hs := hs) (hd := hd) (ha := ha)


/-! ## whole seq function-body closure -/

/-- lite boundary 上の `seq` function-body closure theorem. -/
theorem seq_function_body_closure_lite
    {Γ Δ : TypeEnv} {σ : State} {s t : CppStmt}
    {P₁ : StmtBodyProfileLite Γ s}
    {P₂ : StmtBodyProfileLite Δ t}
    {hN : HasTypeStmtCI .normalK Γ s Δ}
    (h : BodyClosureBoundaryLite Γ σ (.seq s t))
    (hprof : h.profile = .seq hN P₁ P₂)
    (hleft :
      BodyClosureBoundaryLite Γ σ s →
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s)
    (htail :
      ∀ {σ'}, BigStepStmt σ s .normal σ' →
      BodyClosureBoundaryLite Δ σ' t →
      (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨ BigStepStmtDiv σ' t) :
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨ BigStepStmtDiv σ (.seq s t) := by
  have hleftBoundary : BodyClosureBoundaryLite Γ σ s :=
    seq_left_boundary_of_seq h hprof
  rcases hleft hleftBoundary with hleftTerm | hleftDiv
  · rcases hleftTerm with ⟨ex, σ₁, hfb⟩
    cases ex with
    | fellThrough =>
        have hstepS : BigStepStmt σ s .normal σ₁ := by
          simpa using (BigStepFunctionBody.to_stmt hfb)
        have htailBoundary : BodyClosureBoundaryLite Δ σ₁ t :=
          SeqBoundaryTransportLite.seq_tail_boundary_of_left_normal h hprof hstepS
        rcases htail hstepS htailBoundary with htailTerm | htailDiv
        · rcases htailTerm with ⟨ex₂, σ₂, hfb₂⟩
          cases ex₂ with
          | fellThrough =>
              left
              refine ⟨.fellThrough, σ₂, ?_⟩
              apply BigStepFunctionBody.fallthrough
              exact BigStepStmt.seqNormal hstepS (by simpa using (BigStepFunctionBody.to_stmt hfb₂))
          | returned rv =>
              left
              refine ⟨.returned rv, σ₂, ?_⟩
              apply BigStepFunctionBody.returning
              exact BigStepStmt.seqNormal hstepS (by simpa using (BigStepFunctionBody.to_stmt hfb₂))
        · right
          exact BigStepStmtDiv.seqRight hstepS htailDiv
    | returned rv =>
        left
        refine ⟨.returned rv, σ₁, ?_⟩
        apply BigStepFunctionBody.returning
        exact BigStepStmt.seqReturn (by simpa using (BigStepFunctionBody.to_stmt hfb))
  · right
    exact BigStepStmtDiv.seqLeft hleftDiv

end SeqFunctionBodyClosureLite
end Cpp
