import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.Foundation.BodyBoundaryCoherenceV2

Coherence facts showing that the integrated witness `BodyReadyCI` and the
assembled boundary object `BodyClosureBoundaryCI` are two presentations of the
same mathematical content.

This is important before committing to concrete external routes:
we first show that changing presentation does not change the object.
-/

theorem bodyClosureBoundaryCI_roundtrip
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    h.toBodyReadyCI.toClosureBoundary = h := by
  cases h
  rfl

theorem bodyReadyCI_roundtrip
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    h.toClosureBoundary.toBodyReadyCI = h := by
  cases h
  rfl

theorem blockBodyClosureBoundaryCI_roundtrip
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyClosureBoundaryCI Γ σ ss) :
    h.toBlockBodyReadyCI.toClosureBoundary = h := by
  cases h
  rfl

theorem blockBodyReadyCI_roundtrip
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    h.toClosureBoundary.toBlockBodyReadyCI = h := by
  cases h
  rfl

end Cpp
