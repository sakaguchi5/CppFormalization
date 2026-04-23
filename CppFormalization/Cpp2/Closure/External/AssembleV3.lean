import CppFormalization.Cpp2.Closure.External.AdequacyContractsV3

namespace Cpp

/-!
# Closure.External.AssembleV3

Visible entry object for the V3 external assembly layer.

Public-route policy after locating the remaining lie:

- explicit glue route remains available as a low-level specialization;
- generic `Compat -> canonicalGlueV3` route remains available as a *provisional*
  shortcut inherited from `AdequacyKernelV3`;
- the honest public canonical route is now the contract-based route
  `Compat + CanonicalAdequacyContractsV3 -> canonicalGlueV3_ofContracts`.
-/

/-- Explicit low-level external package. -/
structure ExternalPiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  entry : BodyEntryWitness Γ st
  profile : BodyControlProfile Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  core : CoreBigStepFragment st
  adequacy : BodyAdequacyCI Γ σ st profile

/-- Official assembled closure boundary extracted from explicit pieces. -/
def ExternalPiecesV3.toBodyBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  { structural := p.structural
    entry := p.entry
    profile := p.profile
    dynamic := p.dynamic
    adequacy := p.adequacy }

/-- Original low-level route using an explicit glue object. -/
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
  let hrun : RuntimePiecesV3 Γ σ st := F.mkRuntime huse hsuppRun
  let hrefl : ReflectionPiecesV3 Γ st := R.mkReflection hgen hsuppRefl
  let hadeq : BodyAdequacyCI Γ σ st hrefl.profile :=
    G.mkAdequacy huse hsuppRun hgen hsuppRefl hcompat
  exact
    { structural := hrefl.structural
      entry := hrefl.entry
      profile := hrefl.profile
      dynamic := hrun.dynamic
      core := hrefl.core
      adequacy := hadeq }

/-- Original low-level boundary route using an explicit glue object. -/
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
Provisional shortcut inherited from `AdequacyKernelV3`.

This route is retained for compatibility, but it should no longer be treated as
the honest canonical surface.
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

/-- Provisional shortcut boundary route inherited from `AdequacyKernelV3`. -/
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
Honest canonical route:
build the glue object from the explicit pair of adequacy contracts.
-/
noncomputable def assembleExternalPiecesFromContractsV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
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
    (canonicalGlueV3_ofContracts (F := F) (R := R) Compat H)
    huse hsuppRun hgen hsuppRefl hcompat

/-- Honest canonical boundary route from explicit contracts. -/
noncomputable def assembleBodyBoundaryFromContractsV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (assembleExternalPiecesFromContractsV3
    (F := F) (R := R) Compat H
    huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary

/-- The contract-based route is definitionally the explicit route with `canonicalGlueV3_ofContracts`. -/
theorem assembleExternalPiecesFromContractsV3_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    assembleExternalPiecesFromContractsV3
      (F := F) (R := R) Compat H
      huse hsuppRun hgen hsuppRefl hcompat
      =
    assembleExternalPiecesV3
      (F := F) (R := R)
      (canonicalGlueV3_ofContracts (F := F) (R := R) Compat H)
      huse hsuppRun hgen hsuppRefl hcompat := by
  rfl

/-- Likewise for the assembled boundary. -/
theorem assembleBodyBoundaryFromContractsV3_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    assembleBodyBoundaryFromContractsV3
      (F := F) (R := R) Compat H
      huse hsuppRun hgen hsuppRefl hcompat
      =
    assembleBodyBoundaryV3
      (F := F) (R := R)
      (canonicalGlueV3_ofContracts (F := F) (R := R) Compat H)
      huse hsuppRun hgen hsuppRefl hcompat := by
  rfl

end Cpp
