import CppFormalization.Cpp2.Closure.External.GlueV3

namespace Cpp

/-!
# Closure.External.AssembleV3

Assemble target-indexed V3 external pieces into the official mainline entry
object.

Important design point:
- V3 keeps the explicit visible pieces of V2.
- It restores target-indexed applicability assumptions (`supports*`) so that
  concrete artifacts do not appear unrealistically universal.
- `BodyClosureBoundaryCI` is still built definitionally via
  `mkBodyClosureBoundaryCI`.
-/

structure ExternalPiecesV3
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  core : CoreBigStepFragment st
  adequacy : BodyAdequacyCI Γ σ st profile

def ExternalPiecesV3.toBodyBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  mkBodyClosureBoundaryCI
    p.structural
    p.profile
    p.dynamic
    p.adequacy

def assembleExternalPiecesV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    ExternalPiecesV3 Γ σ st := by
  let hd : BodyDynamicBoundary Γ σ st := F.mkDynamic huse hsuppDyn
  let hs : BodyStructuralBoundary Γ st := R.mkStructural hgen hsuppStruct
  let hp : BodyControlProfile Γ st := R.mkProfile hgen hsuppProf
  let hc : CoreBigStepFragment st := R.mkCore hgen
  let ha : BodyAdequacyCI Γ σ st hp :=
    G.mkAdequacy huse hsuppDyn hgen hsuppStruct hsuppProf hcompat hd hs hp hc
  exact
    { structural := hs
      profile := hp
      dynamic := hd
      core := hc
      adequacy := ha }

def assembleBodyBoundaryV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (assembleExternalPiecesV3 G huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toBodyBoundary

end Cpp
