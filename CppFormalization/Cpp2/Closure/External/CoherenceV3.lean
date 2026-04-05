import CppFormalization.Cpp2.Closure.External.AssembleV3

namespace Cpp

/-!
# Closure.External.CoherenceV3

Stage 2B starts by separating two notions that were previously easy to conflate.

* `BoundaryCoherentV3` is the official quotient for closure theorems.
  It says two external presentations induce the same `BodyClosureBoundaryCI`.
* `PackageCoherentV3` is a stronger visible-package comparison notion.
  It keeps only the runtime/reflection-facing observable package fields
  `(dynamic, structural, profile)` and ignores adequacy transport details.

The point is not that one notion subsumes the other definitionally in all
contexts. Rather, the external layer should state clearly which notion each
route-comparison theorem is actually proving.
-/

structure VisiblePiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  dynamic : BodyDynamicBoundary Γ σ st


def ExternalPiecesV3.toVisiblePieces
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) : VisiblePiecesV3 Γ σ st :=
  { structural := p.structural
    profile := p.profile
    dynamic := p.dynamic }


def visiblePiecesOfPackagesV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hrun : RuntimePiecesV3 Γ σ st)
    (hrefl : ReflectionPiecesV3 Γ st) :
    VisiblePiecesV3 Γ σ st :=
  { structural := hrefl.structural
    profile := hrefl.profile
    dynamic := hrun.dynamic }


def canonicalVisiblePiecesV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st) :
    VisiblePiecesV3 Γ σ st :=
  visiblePiecesOfPackagesV3 (F.mkRuntime huse hsuppRun) (R.mkReflection hgen hsuppRefl)


def BoundaryCoherentV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p q : ExternalPiecesV3 Γ σ st) : Prop :=
  p.toBodyBoundary = q.toBodyBoundary


def PackageCoherentV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p q : VisiblePiecesV3 Γ σ st) : Prop :=
  p = q


@[refl] theorem BoundaryCoherentV3.refl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    BoundaryCoherentV3 p p :=
  rfl


@[refl] theorem PackageCoherentV3.refl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : VisiblePiecesV3 Γ σ st) :
    PackageCoherentV3 p p :=
  rfl


theorem PackageCoherentV3.structural_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : VisiblePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.structural = q.structural := by
  cases h
  rfl


theorem PackageCoherentV3.profile_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : VisiblePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.profile = q.profile := by
  cases h
  rfl


theorem PackageCoherentV3.dynamic_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : VisiblePiecesV3 Γ σ st}
    (h : PackageCoherentV3 p q) :
    p.dynamic = q.dynamic := by
  cases h
  rfl

end Cpp
