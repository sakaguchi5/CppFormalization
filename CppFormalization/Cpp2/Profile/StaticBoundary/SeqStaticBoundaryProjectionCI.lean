import CppFormalization.Cpp2.Profile.StaticBoundary.BodyStaticBoundaryCI
import CppFormalization.Cpp2.Static.SeqStatic.SeqTypingProvenanceCI

namespace Cpp

/-!
# Seq static boundary projection

Static projections for `seq`.

The public subject is now `BodyStaticBoundaryCI Γ (.seq s t)`, not
`BodyClosureBoundaryCI Γ σ (.seq s t)`.  This file therefore does not depend on
runtime state, dynamic readiness, semantic adequacy, or closure-boundary
orchestration.

Transitional `BodyClosureBoundaryCI`-indexed wrappers belong in
`Closure.Internal.SeqBoundaryStaticDecompositionCI`, not here.
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
The left side of a statically bounded sequence is well typed.

This is a static projection from `BodyStaticBoundaryCI`, not a closure-boundary
projection.  The compatibility wrapper from a full `BodyClosureBoundaryCI` lives
above this file.
-/
theorem seq_left_typed0_of_static
    {Γ : TypeEnv} {s t : CppStmt}
    (hstatic : BodyStaticBoundaryCI Γ (.seq s t)) :
    WellTypedFrom Γ s := by
  rcases hstatic.typed0 with ⟨Δ, htySeq⟩
  cases htySeq with
  | seq hs _ht =>
      exact ⟨_, hs⟩

end Cpp
