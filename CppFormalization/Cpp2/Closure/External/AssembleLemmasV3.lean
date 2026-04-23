import CppFormalization.Cpp2.Closure.External.AssembleV3
import CppFormalization.Cpp2.Closure.External.CoherenceV3

namespace Cpp

/-!
# Closure.External.AssembleLemmasV3

Projection and view lemmas for the low-level assembly route.

These are route-generic facts about `assembleExternalPiecesV3`, so they belong
next to the assembly layer rather than inside any concrete family.
-/

theorem assembleExternalPiecesV3_structural
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).structural =
      (R.mkReflection hgen hsuppRefl).structural := by
  unfold assembleExternalPiecesV3
  rfl

theorem assembleExternalPiecesV3_entry
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).static=
      (R.mkReflection hgen hsuppRefl).static := by
  --unfold assembleExternalPiecesV3
  rfl

theorem assembleExternalPiecesV3_dynamic
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).dynamic =
      (F.mkRuntime huse hsuppRun).dynamic := by
  unfold assembleExternalPiecesV3
  rfl

theorem assembleExternalPiecesV3_core
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).core =
      (R.mkReflection hgen hsuppRefl).core := by
  unfold assembleExternalPiecesV3
  rfl

theorem assembleExternalPiecesV3_adequacy
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).adequacy =
      G.mkAdequacy huse hsuppRun hgen hsuppRefl hcompat := by
  unfold assembleExternalPiecesV3
  rfl
/-
theorem assembleExternalPiecesV3_toVisiblePieces
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat) =
      canonicalVisiblePiecesV3 huse hsuppRun hgen hsuppRefl := by
  rfl

theorem assembleExternalPiecesV3_packageCoherent
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    PackageCoherentV3
      (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces
      (canonicalVisiblePiecesV3 huse hsuppRun hgen hsuppRefl) := by
  rfl
-/


end Cpp
