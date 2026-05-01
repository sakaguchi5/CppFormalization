import CppFormalization.Cpp2.Closure.Internal.BlockBodyFunctionClosureLite
import CppFormalization.Cpp2.Closure.Internal.Transport.BlockBodyBoundaryTransportLite
import CppFormalization.Cpp2.Lemmas.BigStepScopeDepth
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp
namespace BlockFunctionBodyClosureLite

/-!
# Closure.Internal.BlockFunctionBodyClosureLite_recursor

Statement-level block closure wrapper for the lite opened-block-body route.

The general scope-depth / closeability recursor facts live in
`Cpp2.Lemmas.BigStepScopeDepth`; this file only assembles the lite closure result.
-/

@[simp] theorem bigStepFunctionBlockBody_fellThrough_iff
    {σ σ' : State} {ss : StmtBlock} :
    BigStepFunctionBlockBody σ ss .fellThrough σ' ↔
      BigStepBlock σ ss .normal σ' := by
  constructor
  · intro h
    cases h with
    | fallthrough hblk => exact hblk
  · intro hblk
    exact BigStepFunctionBlockBody.fallthrough hblk

@[simp] theorem bigStepFunctionBlockBody_returned_iff
    {σ σ' : State} {ss : StmtBlock} {rv : Option Value} :
    BigStepFunctionBlockBody σ ss (.returned rv) σ' ↔
      BigStepBlock σ ss (.returnResult rv) σ' := by
  constructor
  · intro h
    cases h with
    | returning hblk => exact hblk
  · intro hblk
    exact BigStepFunctionBlockBody.returning hblk

theorem block_function_body_closure_lite
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyProfileLite (pushTypeScope Γ) ss}
    (h : BodyClosureBoundaryLite Γ σ (.block ss))
    (hprof : h.profile = .block P)
    (hbody :
      ∀ {σ'}, OpenScope σ σ' →
      BlockBodyClosureBoundaryLite (pushTypeScope Γ) σ' ss →
      (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨ BigStepStmtDiv σ (.block ss) := by
  let σ₁ := pushScope σ
  have hopen : OpenScope σ σ₁ := by
    rfl
  have hopened : BlockBodyClosureBoundaryLite (pushTypeScope Γ) σ₁ ss :=
    BlockBodyBoundaryTransportLite.blockBodyBoundaryLite_of_bodyClosureBoundaryLite_opened
      h hprof hopen
  rcases hbody hopen hopened with hterm | hdiv
  · rcases hterm with ⟨ex, σ₂, hfb⟩
    cases ex with
    | fellThrough =>
        have hblk : BigStepBlock σ₁ ss .normal σ₂ := by
          simpa using hfb
        have hnePush : σ₁.scopes ≠ [] := by
          simp [σ₁, pushScope]
        have hne₂ : σ₂.scopes ≠ [] :=
          block_preserves_nonempty_scopes hblk hnePush
        have hexClose : ∃ σ₃, CloseScope σ₂ σ₃ := by
          simpa [closeScope_eq_popScope] using (popScope?_some_iff σ₂).2 hne₂
        rcases hexClose with ⟨σ₃, hclose⟩
        left
        refine ⟨.fellThrough, σ₃, ?_⟩
        apply BigStepFunctionBody.fallthrough
        exact BigStepStmt.block hopen hblk hclose
    | returned rv =>
        have hblk : BigStepBlock σ₁ ss (.returnResult rv) σ₂ := by
          simpa using hfb
        have hnePush : σ₁.scopes ≠ [] := by
          simp [σ₁, pushScope]
        have hne₂ : σ₂.scopes ≠ [] :=
          block_preserves_nonempty_scopes hblk hnePush
        have hexClose : ∃ σ₃, CloseScope σ₂ σ₃ := by
          simpa [closeScope_eq_popScope] using (popScope?_some_iff σ₂).2 hne₂
        rcases hexClose with ⟨σ₃, hclose⟩
        left
        refine ⟨.returned rv, σ₃, ?_⟩
        apply BigStepFunctionBody.returning
        exact BigStepStmt.block hopen hblk hclose
  · right
    exact BigStepStmtDiv.block hopen hdiv

end BlockFunctionBodyClosureLite
end Cpp
