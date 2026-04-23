import CppFormalization.Cpp2.Closure.External.AdequacyContractsV3

namespace Cpp

/-!
# Closure.External.AssembleV3

Visible V3 assembly after the static-layer redesign.
-/

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

abbrev VisiblePiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) :=
  ExternalPiecesV3 Γ σ st

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
