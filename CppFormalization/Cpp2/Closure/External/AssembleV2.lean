import CppFormalization.Cpp2.Closure.External.GlueV2

namespace Cpp

/-!
# Closure.External.AssembleV2

Assemble explicit external pieces into the official mainline entry object.

Important design point:
- `structural`, `profile`, `dynamic`, and `core` are exposed as visible pieces.
- `adequacy` is exposed as an explicit dependent glue component over `profile`.
- `BodyClosureBoundaryCI` is built definitionally via `mkBodyClosureBoundaryCI`.
-/

structure ExternalPieces (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

def ExternalPieces.toBodyBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPieces Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  { structural := p.structural
    static := p.static
    dynamic := p.dynamic
    adequacy := p.adequacy }

def assembleExternalPieces
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hgen : R.generates m st)
    (hcompat : G.compatible n m Γ σ st) :
    ExternalPieces Γ σ st := by
  sorry
  /-
  let hd : BodyDynamicBoundary Γ σ st := F.mkDynamic huse
  let hs : BodyStructuralBoundary Γ st := R.mkStructural hgen
  let he : BodyEntryWitness Γ st := R.mkEntry hgen
  let hp : BodyControlProfile Γ st := R.mkProfile hgen
  let hc : CoreBigStepFragment st := R.mkCore hgen
  let ha : BodyAdequacyCI Γ σ st hp :=
    G.mkAdequacy hcompat hd hs hp hc
  exact
    { structural := hs
      entry := he
      profile := hp
      dynamic := hd
      core := hc
      adequacy := ha }-/

def assembleBodyBoundary
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hgen : R.generates m st)
    (hcompat : G.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (assembleExternalPieces G huse hgen hcompat).toBodyBoundary


end Cpp
