import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.External.AssembleV3

The visible entry object stays the same:
explicit pieces plus `toBodyBoundary`.

What changes after introducing `AdequacyKernelV3` is that we now support two
low-level entry routes:

1. explicit glue route:
   - caller provides `G : VerifiedExternalGlueV3 F R`,
   - assembly uses `G.mkAdequacy` directly.

2. canonical-compatibility route:
   - caller provides only a compatibility predicate `Compat`,
   - assembly builds the canonical glue object `canonicalGlueV3 Compat`,
   - then reuses the same explicit glue route.

This keeps the old API working while adding the cleaner post-kernel route.
-/

/-- Explicit low-level external package. -/
structure ExternalPiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  core : CoreBigStepFragment st
  adequacy : BodyAdequacyCI Γ σ st profile

/-- Official assembled closure boundary extracted from explicit pieces. -/
def ExternalPiecesV3.toBodyBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  mkBodyClosureBoundaryCI
    p.structural
    p.profile
    p.dynamic
    p.adequacy

/--
Assemble explicit pieces from an explicit glue object.
This is the original Stage 2A low-level route and remains useful.
-/
noncomputable def assembleExternalPiecesV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    ExternalPiecesV3 Γ σ st := by
  let hrun : RuntimePiecesV3 Γ σ st :=
    F.mkRuntime huse hsuppRun
  let hrefl : ReflectionPiecesV3 Γ st :=
    R.mkReflection hgen hsuppRefl
  let hadeq : BodyAdequacyCI Γ σ st hrefl.profile :=
    G.mkAdequacy huse hsuppRun hgen hsuppRefl hcompat
  exact
    { structural := hrefl.structural
      profile := hrefl.profile
      dynamic := hrun.dynamic
      core := hrefl.core
      adequacy := hadeq }

/-- The corresponding official boundary from the explicit glue route. -/
noncomputable def assembleBodyBoundaryV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary

/--
Canonical low-level assembly route:
use only a compatibility predicate, build the canonical glue object from
`AdequacyKernelV3`, and then reuse the explicit glue route.
-/
noncomputable def assembleExternalPiecesFromCompatV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    ExternalPiecesV3 Γ σ st :=
  assembleExternalPiecesV3
    (F := F) (R := R)
    (canonicalGlueV3 (F := F) (R := R) Compat)
    huse hsuppRun hgen hsuppRefl hcompat

/-- The corresponding official boundary from the canonical compatibility route. -/
noncomputable def assembleBodyBoundaryFromCompatV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (assembleExternalPiecesFromCompatV3
    (F := F) (R := R) Compat
    huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary

/--
The canonical compatibility route is definitionally the explicit glue route with
`canonicalGlueV3 Compat`.
-/
theorem assembleExternalPiecesFromCompatV3_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    assembleExternalPiecesFromCompatV3
      (F := F) (R := R) Compat
      huse hsuppRun hgen hsuppRefl hcompat
      =
    assembleExternalPiecesV3
      (F := F) (R := R)
      (canonicalGlueV3 (F := F) (R := R) Compat)
      huse hsuppRun hgen hsuppRefl hcompat := by
  rfl

/--
Likewise for the assembled official boundary.
-/
theorem assembleBodyBoundaryFromCompatV3_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    assembleBodyBoundaryFromCompatV3
      (F := F) (R := R) Compat
      huse hsuppRun hgen hsuppRefl hcompat
      =
    assembleBodyBoundaryV3
      (F := F) (R := R)
      (canonicalGlueV3 (F := F) (R := R) Compat)
      huse hsuppRun hgen hsuppRefl hcompat := by
  rfl

end Cpp
