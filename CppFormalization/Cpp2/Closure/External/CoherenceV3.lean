import CppFormalization.Cpp2.Closure.External.AssembleV3

namespace Cpp

/-!
# Closure.External.CoherenceV3

Stage 2B separates two comparison notions.

* `BoundaryCoherentV3` is the official quotient for closure theorems.
  It compares the induced `BodyClosureBoundaryCI`.

* `PackageCoherentV3` compares the official observable package surface.
  After the static-layer redesign this observable surface contains the whole
  `BodyStaticBoundaryCI`, not just its profile.

There is deliberately no `VisiblePiecesV3` in this layer.  The former visible
view has been replaced by `ObservablePiecesV3`; profile-only comparisons are
kept outside the official package carrier.
-/

/-- Assemble the official observable view directly from runtime/reflection packages. -/
def observablePiecesOfPackagesV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hrun : RuntimePiecesV3 Γ σ st)
    (hrefl : ReflectionPiecesV3 Γ st) :
    ObservablePiecesV3 Γ σ st :=
  { structural := hrefl.structural
    static := hrefl.static
    dynamic := hrun.dynamic }

/-- Canonical observable package chosen by the std/reflection fragments. -/
def canonicalObservablePiecesV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st) :
    ObservablePiecesV3 Γ σ st :=
  observablePiecesOfPackagesV3
    (F.mkRuntime huse hsuppRun)
    (R.mkReflection hgen hsuppRefl)

/-- Official quotient used by closure theorems. -/
def BoundaryCoherentV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p q : ExternalPiecesV3 Γ σ st) : Prop :=
  p.toBodyBoundary = q.toBodyBoundary

/-- Strong observable-package comparison. -/
def PackageCoherentV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p q : ObservablePiecesV3 Γ σ st) : Prop :=
  p = q

@[refl] theorem BoundaryCoherentV3.refl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    BoundaryCoherentV3 p p := rfl

@[refl] theorem PackageCoherentV3.refl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ObservablePiecesV3 Γ σ st) :
    PackageCoherentV3 p p := rfl

theorem PackageCoherentV3.structural_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : ObservablePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.structural = q.structural := by
  cases h
  rfl

theorem PackageCoherentV3.static_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : ObservablePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.static = q.static := by
  cases h
  rfl

/-- Profile equality is only a projection of official static-package coherence. -/
theorem PackageCoherentV3.static_profile_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : ObservablePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.static.profile = q.static.profile := by
  exact congrArg BodyStaticBoundaryCI.profile
    (PackageCoherentV3.static_eq h)

/-- Compatibility alias.  Prefer `PackageCoherentV3.static_profile_eq`. -/
theorem PackageCoherentV3.profile_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : ObservablePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.static.profile = q.static.profile :=
  PackageCoherentV3.static_profile_eq h

theorem PackageCoherentV3.dynamic_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : ObservablePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.dynamic = q.dynamic := by
  cases h
  rfl

end Cpp
