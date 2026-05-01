import CppFormalization.Cpp2.Closure.External.AdequacyContractsV3

namespace Cpp

/-!
# Closure.External.AssembleV3

Observable V3 assembly after the static-layer redesign.

`VisiblePiecesV3` is intentionally not defined here.  The official package-level
view is `ObservablePiecesV3`; the full external package is `ExternalPiecesV3`.
-/

/--
The official observable package view used by `PackageCoherentV3`.

Important: this is no longer profile-only.  The static package is observed as
one coherent unit, because `typed0`, `root`, and `profile` must not be compared
independently after the static-layer redesign.
-/
structure ObservablePiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  dynamic : BodyDynamicBoundary Γ σ st

/--
A weaker profile-only view.

This exists only for diagnostics or explicitly legacy/profile-only comparison
statements.  It must not be used as the carrier of `PackageCoherentV3` or as the
main route-coherence notion.
-/
structure ProfileObservablePiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  dynamic : BodyDynamicBoundary Γ σ st

namespace ObservablePiecesV3

def toProfileObservable
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ObservablePiecesV3 Γ σ st) :
    ProfileObservablePiecesV3 Γ σ st :=
  { structural := p.structural
    profile := p.static.profile
    dynamic := p.dynamic }

end ObservablePiecesV3
structure ExternalPiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  core : CoreBigStepFragment st
  adequacy : BodyAdequacyCI Γ σ st static.profile

namespace ExternalPiecesV3

def toBodyBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  mkBodyClosureBoundaryCI
    p.structural
    p.static
    p.dynamic
    p.adequacy

def toObservablePieces
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    ObservablePiecesV3 Γ σ st :=
  { structural := p.structural
    static := p.static
    dynamic := p.dynamic }

def toProfileObservablePieces
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    ProfileObservablePiecesV3 Γ σ st :=
  p.toObservablePieces.toProfileObservable

end ExternalPiecesV3

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
  let hadeq : BodyAdequacyCI Γ σ st hrefl.static.profile :=
    G.mkAdequacy huse hsuppRun hgen hsuppRefl hcompat
  exact
    { structural := hrefl.structural
      static := hrefl.static
      dynamic := hrun.dynamic
      core := hrefl.core
      adequacy := hadeq }

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

theorem assembleExternalPiecesV3_toBodyBoundary
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    let hrun := F.mkRuntime huse hsuppRun
    let hrefl := R.mkReflection hgen hsuppRefl
    (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary =
      mkBodyClosureBoundaryCI
        hrefl.structural
        hrefl.static
        hrun.dynamic
        (G.mkAdequacy huse hsuppRun hgen hsuppRefl hcompat) := by
  rfl

end Cpp
