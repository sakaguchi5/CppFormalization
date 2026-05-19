import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Static.Pure.SeqTypingProvenanceCI

namespace Cpp

/-!
# Seq static boundary projection

Transitional boundary/static projections for `seq`.

This file is deliberately outside `Static/Pure`: it still receives a
`BodyClosureBoundaryCI` because the current API uses the assembled closure
boundary as the carrier of structural/static profile data.
-/

/--
Static scaffold for the left side of a sequence, excluding the old `typed0`
payload.

`typed0` is theorem-backed from the whole sequence's coarse typing below.
The remaining static data is the chosen CI profile/root/coherence for `s`.
-/
structure SeqLeftStaticScaffoldCI
    (Γ : TypeEnv) (s : CppStmt) : Type where
  profile : BodyControlProfile Γ s
  root : BodyEntryWitness Γ s
  rootCoherent : BodyRootCoherent profile root

namespace SeqLeftStaticScaffoldCI

/-- Assemble the canonical left static boundary from theorem-backed `typed0`. -/
def toBodyStaticBoundaryCI
    {Γ : TypeEnv} {s : CppStmt}
    (h : SeqLeftStaticScaffoldCI Γ s)
    (htyped : WellTypedFrom Γ s) :
    BodyStaticBoundaryCI Γ s :=
  { typed0 := htyped
    profile := h.profile
    root := h.root
    rootCoherent := h.rootCoherent }

end SeqLeftStaticScaffoldCI

/--
The left side of a well-typed sequence is well typed.

This is deliberately proved from the coarse `typed0` payload of the whole
sequence. It is not guessed from a CI root witness, because a return/break root
by itself does not generally carry enough information to type unrelated sequence
tails.
-/
theorem seq_left_typed0_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    WellTypedFrom Γ s := by
  rcases hentry.static.typed0 with ⟨Δ, htySeq⟩
  cases htySeq with
  | seq hs _ht =>
      exact ⟨_, hs⟩

/-- The left side inherits structural admissibility from the whole sequence. -/
theorem seq_left_structural_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStructuralBoundary Γ s := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/-- The tail side inherits structural admissibility from the whole sequence. -/
theorem seq_tail_structural_boundary_of_entry
    {Γ Θ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStructuralBoundary Θ t := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.2
      breakScoped := hbreak.2
      continueScoped := hcont.2 }

end Cpp
