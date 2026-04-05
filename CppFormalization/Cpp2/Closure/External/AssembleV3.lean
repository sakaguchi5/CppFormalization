import CppFormalization.Cpp2.Closure.External.GlueV3

namespace Cpp

/-!
# Closure.External.AssembleV3

The visible entry object stays the same: explicit pieces plus `toBodyBoundary`.
What changes in Stage 2A is where those pieces come from.
-/

structure ExternalPiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  core : CoreBigStepFragment st
  adequacy : BodyAdequacyCI Γ σ st profile


def ExternalPiecesV3.toBodyBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) : BodyClosureBoundaryCI Γ σ st :=
  mkBodyClosureBoundaryCI p.structural p.profile p.dynamic p.adequacy


def assembleExternalPiecesV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
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
      profile := hrefl.profile
      dynamic := hrun.dynamic
      core := hrefl.core
      adequacy := hadeq }


def assembleBodyBoundaryV3
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

end Cpp
