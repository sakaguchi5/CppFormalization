import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary

namespace Cpp

/-!
# Seq structural projection

Pure structural projections for `seq`.

The public subject is `BodyStructuralBoundary`, not `BodyClosureBoundaryCI`.
This keeps structural projection independent of closure, dynamic readiness,
semantic adequacy, and runtime state.
-/

/-- The left side inherits structural admissibility from the whole sequence. -/
theorem seq_left_structural_boundary_of_structural
    {Γ : TypeEnv} {s t : CppStmt}
    (hstruct : BodyStructuralBoundary Γ (.seq s t)) :
    BodyStructuralBoundary Γ s := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hstruct.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hstruct.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hstruct.continueScoped
  exact
    { wf := hwf.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/-- The tail side inherits structural admissibility from the whole sequence. -/
theorem seq_tail_structural_boundary_of_structural
    {Γ Θ : TypeEnv} {s t : CppStmt}
    (hstruct : BodyStructuralBoundary Γ (.seq s t)) :
    BodyStructuralBoundary Θ t := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hstruct.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hstruct.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hstruct.continueScoped
  exact
    { wf := hwf.2
      breakScoped := hbreak.2
      continueScoped := hcont.2 }

end Cpp
