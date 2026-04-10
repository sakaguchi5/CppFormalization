import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.External.AssembleV3

The visible entry object stays the same: explicit pieces plus `toBodyBoundary`.

Public-route policy after the compatibility-kernel refactor:
- the explicit glue route remains available as a low-level specialization,
- the compatibility route is the canonical public route,
- both land in the same `ExternalPiecesV3` / `BodyClosureBoundaryCI` objects.
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
  mkBodyClosureBoundaryCI p.structural p.profile p.dynamic p.adequacy

/-- Original low-level route using an explicit glue object. -/
noncomputable def assembleExternalPiecesV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
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

/-- Original low-level boundary route using an explicit glue object. -/
noncomputable def assembleBodyBoundaryV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary

/-- Canonical route: build the glue object from a compatibility predicate. -/
noncomputable def assembleExternalPiecesFromCompatV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
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

/-- Canonical boundary route: build the glue object from a compatibility predicate. -/
noncomputable def assembleBodyBoundaryFromCompatV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (assembleExternalPiecesFromCompatV3
    (F := F) (R := R) Compat
    huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary

/-- The canonical route is definitionally the explicit route with `canonicalGlueV3 Compat`. -/
theorem assembleExternalPiecesFromCompatV3_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
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

/-- Likewise for the assembled boundary. -/
theorem assembleBodyBoundaryFromCompatV3_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
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
