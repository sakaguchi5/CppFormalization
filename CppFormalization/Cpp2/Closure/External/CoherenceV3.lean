import CppFormalization.Cpp2.Closure.External.AssembleV3

namespace Cpp

/-!
# Closure.External.CoherenceV3

Stage 2B temporarily separates two notions that were previously easy to conflate.

* `BoundaryCoherentV3` is the official quotient for closure theorems.
  It says two external presentations induce the same `BodyClosureBoundaryCI`.

* `PackageCoherentV3` is a stronger observable-package comparison notion.
  For now, we keep the old observable view `(dynamic, structural, profile)`,
  but we rename its carrier type to avoid clashing with the new
  `ExternalPiecesV3.VisiblePiecesV3` abbreviation introduced in `AssembleV3`.

This is an intentional temporary isolation patch.
The long-term redesign question is postponed.
-/



/-- Forget the full external package down to the temporary observable view. -/
def ExternalPiecesV3.toObservablePieces
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    ObservablePiecesV3 Γ σ st :=
  { structural := p.structural
    profile := p.static.profile
    dynamic := p.dynamic }

/-- Assemble the temporary observable view directly from runtime/reflection packages. -/
def observablePiecesOfPackagesV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hrun : RuntimePiecesV3 Γ σ st)
    (hrefl : ReflectionPiecesV3 Γ st) :
    ObservablePiecesV3 Γ σ st :=
  { structural := hrefl.structural
    profile := hrefl.static.profile
    dynamic := hrun.dynamic }

/-- Canonical temporary observable package chosen by the std/reflection fragments. -/
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

/-- Stronger temporary observable-package comparison notion. -/
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

theorem PackageCoherentV3.profile_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : ObservablePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.profile = q.profile := by
  cases h
  rfl

theorem PackageCoherentV3.dynamic_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : ObservablePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.dynamic = q.dynamic := by
  cases h
  rfl

end Cpp
