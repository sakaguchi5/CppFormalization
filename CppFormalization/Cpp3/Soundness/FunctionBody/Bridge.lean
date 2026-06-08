import CppFormalization.Cpp3.Soundness.Structural.Driver
import CppFormalization.Cpp3.Semantics.ControlAdequacy

/-!
# CppFormalization.Cpp3.Soundness.FunctionBody.Bridge

Bridge from statement closed soundness to function-body closed soundness.

This bridge is intentionally not the false general theorem
`ClosedStmtSoundness → ClosedFunctionBodySoundness`.  It uses the static
function-body control surface to exclude escaping top-level `break` and
`continue`, exactly as C++ function bodies require.
-/

namespace Cpp3
namespace Soundness
namespace FunctionBody

/-- Runtime control safety induced by a function-body boundary. -/
def FunctionBodyControlSafe (σ : State) (body : CppStmt) : Prop :=
  ∀ {r : CtrlResult} {σ₁ : State},
    Semantics.BigStepStmt σ body r σ₁ →
      Semantics.FunctionBodyAcceptableStmtResult r

/-- Static function-body boundary information induces runtime control safety. -/
theorem controlSafe_of_staticFunctionBodyBoundaryInfo
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (hstatic : Static.StaticFunctionBodyBoundaryInfo Γ body) :
    FunctionBodyControlSafe σ body := by
  intro r σ₁ hstep
  exact
    Semantics.acceptableStmtResult_of_bigStep
      hstatic.control
      hstep
      hstatic.entry.formed

/-- Statement soundness becomes function-body soundness under function-body control safety. -/
theorem closedFunctionBodySoundness_of_closedStmtSoundness_controlSafe
    {σ : State} {body : CppStmt}
    (hstmt : ClosedStmtSoundness σ body)
    (hcontrol : FunctionBodyControlSafe σ body) :
    ClosedFunctionBodySoundness σ body := by
  have hclassified : Semantics.StmtClassified σ body := by
    simpa [ClosedStmtSoundness] using hstmt
  unfold ClosedFunctionBodySoundness
  unfold Semantics.FunctionBodyClassified
  rcases hclassified with hterm | hdiv
  · rcases hterm with ⟨r, σ₁, hstep⟩
    have haccept := hcontrol hstep
    cases r with
    | normal =>
        exact Or.inl
          ⟨ProgSuccess.normal, σ₁,
            Semantics.BigStepFunctionBody.normal hstep⟩
    | breakResult =>
        cases haccept
    | continueResult =>
        cases haccept
    | returnResult ov =>
        exact Or.inl
          ⟨ProgSuccess.returned ov, σ₁,
            Semantics.BigStepFunctionBody.returned hstep⟩
  · exact Or.inr hdiv

/-- Static function-body boundary information is the natural control premise. -/
theorem closedFunctionBodySoundness_of_closedStmtSoundness_static
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (hstatic : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (hstmt : ClosedStmtSoundness σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_of_closedStmtSoundness_controlSafe
    hstmt
    (controlSafe_of_staticFunctionBodyBoundaryInfo hstatic)

/-- Use a concrete function-body boundary to lift statement soundness. -/
theorem closedFunctionBodySoundness_of_stmtBoundarySoundness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body)
    (bodySound : Boundary.StmtBoundary Γ σ body → ClosedStmtSoundness σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_of_closedStmtSoundness_static
    boundary.static
    (bodySound boundary.entry)

/-- Function-body soundness forgets back to statement soundness. -/
theorem closedStmtSoundness_of_closedFunctionBodySoundness
    {σ : State} {body : CppStmt}
    (hbody : ClosedFunctionBodySoundness σ body) :
    ClosedStmtSoundness σ body := by
  unfold ClosedStmtSoundness
  unfold Semantics.StmtClassified
  unfold ClosedFunctionBodySoundness at hbody
  unfold Semantics.FunctionBodyClassified at hbody
  rcases hbody with hterm | hdiv
  · rcases hterm with ⟨success, σ₁, hfb⟩
    cases hfb with
    | normal hstep =>
        exact Or.inl ⟨CtrlResult.normal, σ₁, hstep⟩
    | returned hstep =>
        exact Or.inl ⟨_, σ₁, hstep⟩
  · exact Or.inr hdiv

/-- The structural function-body clause induced by the function-body boundary entry. -/
def structuralFunctionBodyClause :
    Structural.FunctionBodyStructuralSoundnessClause where
  sound := by
    intro Γ σ body boundary bodySound
    exact bodySound boundary.entry



end FunctionBody
end Soundness
end Cpp3
