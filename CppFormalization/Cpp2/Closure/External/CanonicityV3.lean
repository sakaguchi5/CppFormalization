import CppFormalization.Cpp2.Closure.External.CoherenceV3

namespace Cpp

/-!
# Closure.External.CanonicityV3

Stage 2C isolates the next question after Stage 2B route-coherence:

* Stage 2B told us how to compare two external *routes*.
* Stage 2C asks when the runtime / reflection *families themselves* are
  canonical for a fixed target.

The point is not proof-irrelevance of support witnesses.  The point is stronger:
for a fixed target `(Γ, σ, st)` or `(Γ, st)`, different artifact names / metas
that support that same target should not yield different observable packages.

This file therefore records family-level uniqueness / canonicity assumptions and
extracts the visible consequences needed by later builder layers.
-/



/-- For a fixed `(Γ, σ, st)`, the runtime-facing dynamic boundary read off from
two ready witnesses is intrinsic to the target, not to the witness. -/
theorem bodyReadyCI_toDynamic_unique
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (r₁ r₂ : BodyReadyCI Γ σ st) :
    r₁.toDynamic = r₂.toDynamic := by
  cases r₁
  cases r₂
  dsimp [BodyReadyCI.toDynamic]

/-- For a fixed `(Γ, st)`, the structural boundary read off from a ready
witness does not depend on which state-indexed ready proof was chosen. -/
theorem bodyReadyCI_toStructural_unique
    {Γ : TypeEnv} {σ₁ σ₂ : State} {st : CppStmt}
    (r₁ : BodyReadyCI Γ σ₁ st)
    (r₂ : BodyReadyCI Γ σ₂ st) :
    r₁.toStructural = r₂.toStructural := by
  cases r₁
  cases r₂
  dsimp [BodyReadyCI.toStructural]

/-- On a fixed statement target, the core fragment carried by the external V3
route is judgmental rather than choice-dependent. -/
theorem coreBigStepFragment_unique
    {st : CppStmt}
    (c₁ c₂ : CoreBigStepFragment st) :
    c₁ = c₂ := rfl

/-- Runtime package canonicity for a fixed `(Γ, σ, st)` target. -/
def RuntimePackageUniqueV3 (F : VerifiedStdFragmentV3) : Prop :=
  ∀ {n₁ n₂ : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse₁ : F.uses n₁) (hsupp₁ : F.supportsRuntime n₁ Γ σ st)
    (huse₂ : F.uses n₂) (hsupp₂ : F.supportsRuntime n₂ Γ σ st),
    F.mkRuntime huse₁ hsupp₁ = F.mkRuntime huse₂ hsupp₂

/-- Reflection package canonicity for a fixed `(Γ, st)` target. -/
def ReflectionPackageUniqueV3 (R : VerifiedReflectionFragmentV3) : Prop :=
  ∀ {m₁ m₂ : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen₁ : R.generates m₁ st) (hsupp₁ : R.supportsReflection m₁ Γ st)
    (hgen₂ : R.generates m₂ st) (hsupp₂ : R.supportsReflection m₂ Γ st),
    R.mkReflection hgen₁ hsupp₁ = R.mkReflection hgen₂ hsupp₂


theorem RuntimePackageUniqueV3.dynamic_eq
    {F : VerifiedStdFragmentV3}
    (huniq : RuntimePackageUniqueV3 F)
    {n₁ n₂ : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse₁ : F.uses n₁) (hsupp₁ : F.supportsRuntime n₁ Γ σ st)
    (huse₂ : F.uses n₂) (hsupp₂ : F.supportsRuntime n₂ Γ σ st) :
    (F.mkRuntime huse₁ hsupp₁).dynamic =
      (F.mkRuntime huse₂ hsupp₂).dynamic := by
  exact congrArg (fun p => p.dynamic) (huniq huse₁ hsupp₁ huse₂ hsupp₂)


theorem ReflectionPackageUniqueV3.structural_eq
    {R : VerifiedReflectionFragmentV3}
    (huniq : ReflectionPackageUniqueV3 R)
    {m₁ m₂ : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen₁ : R.generates m₁ st) (hsupp₁ : R.supportsReflection m₁ Γ st)
    (hgen₂ : R.generates m₂ st) (hsupp₂ : R.supportsReflection m₂ Γ st) :
    (R.mkReflection hgen₁ hsupp₁).structural =
      (R.mkReflection hgen₂ hsupp₂).structural := by
  exact congrArg (fun p => p.structural) (huniq hgen₁ hsupp₁ hgen₂ hsupp₂)

theorem ReflectionPackageUniqueV3.profile_eq
    {R : VerifiedReflectionFragmentV3}
    (huniq : ReflectionPackageUniqueV3 R)
    {m₁ m₂ : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen₁ : R.generates m₁ st) (hsupp₁ : R.supportsReflection m₁ Γ st)
    (hgen₂ : R.generates m₂ st) (hsupp₂ : R.supportsReflection m₂ Γ st) :
    (R.mkReflection hgen₁ hsupp₁).profile =
      (R.mkReflection hgen₂ hsupp₂).profile := by
  exact congrArg (fun p => p.profile) (huniq hgen₁ hsupp₁ hgen₂ hsupp₂)


theorem ReflectionPackageUniqueV3.core_eq
    {R : VerifiedReflectionFragmentV3}
    (huniq : ReflectionPackageUniqueV3 R)
    {m₁ m₂ : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen₁ : R.generates m₁ st) (hsupp₁ : R.supportsReflection m₁ Γ st)
    (hgen₂ : R.generates m₂ st) (hsupp₂ : R.supportsReflection m₂ Γ st) :
    (R.mkReflection hgen₁ hsupp₁).core =
      (R.mkReflection hgen₂ hsupp₂).core := by
  exact congrArg (fun p => p.core) (huniq hgen₁ hsupp₁ hgen₂ hsupp₂)


theorem canonicalVisiblePiecesV3_wellDefined
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (hrununiq : RuntimePackageUniqueV3 F)
    (hrefluniq : ReflectionPackageUniqueV3 R)
    {n₁ n₂ : F.Name} {m₁ m₂ : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse₁ : F.uses n₁) (hsuppRun₁ : F.supportsRuntime n₁ Γ σ st)
    (hgen₁ : R.generates m₁ st) (hsuppRefl₁ : R.supportsReflection m₁ Γ st)
    (huse₂ : F.uses n₂) (hsuppRun₂ : F.supportsRuntime n₂ Γ σ st)
    (hgen₂ : R.generates m₂ st) (hsuppRefl₂ : R.supportsReflection m₂ Γ st) :
    canonicalObservablePiecesV3 huse₁ hsuppRun₁ hgen₁ hsuppRefl₁ =
      canonicalObservablePiecesV3 huse₂ hsuppRun₂ hgen₂ hsuppRefl₂ := by
  unfold canonicalObservablePiecesV3
  unfold observablePiecesOfPackagesV3
  have hrun : F.mkRuntime huse₁ hsuppRun₁ = F.mkRuntime huse₂ hsuppRun₂ :=
    hrununiq huse₁ hsuppRun₁ huse₂ hsuppRun₂
  have hrefl : R.mkReflection hgen₁ hsuppRefl₁ = R.mkReflection hgen₂ hsuppRefl₂ :=
    hrefluniq hgen₁ hsuppRefl₁ hgen₂ hsuppRefl₂
  calc
    observablePiecesOfPackagesV3
        (F.mkRuntime huse₁ hsuppRun₁)
        (R.mkReflection hgen₁ hsuppRefl₁)
      =
        observablePiecesOfPackagesV3
          (F.mkRuntime huse₂ hsuppRun₂)
          (R.mkReflection hgen₁ hsuppRefl₁) := by
            exact congrArg
              (fun rp =>
                observablePiecesOfPackagesV3 rp (R.mkReflection hgen₁ hsuppRefl₁))
              hrun
    _ =
        observablePiecesOfPackagesV3
          (F.mkRuntime huse₂ hsuppRun₂)
          (R.mkReflection hgen₂ hsuppRefl₂) := by
            exact congrArg
              (fun fp =>
                observablePiecesOfPackagesV3 (F.mkRuntime huse₂ hsuppRun₂) fp)
              hrefl


theorem canonicalVisiblePiecesV3_packageCoherent
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (hrununiq : RuntimePackageUniqueV3 F)
    (hrefluniq : ReflectionPackageUniqueV3 R)
    {n₁ n₂ : F.Name} {m₁ m₂ : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse₁ : F.uses n₁) (hsuppRun₁ : F.supportsRuntime n₁ Γ σ st)
    (hgen₁ : R.generates m₁ st) (hsuppRefl₁ : R.supportsReflection m₁ Γ st)
    (huse₂ : F.uses n₂) (hsuppRun₂ : F.supportsRuntime n₂ Γ σ st)
    (hgen₂ : R.generates m₂ st) (hsuppRefl₂ : R.supportsReflection m₂ Γ st) :
    PackageCoherentV3
      (canonicalObservablePiecesV3 huse₁ hsuppRun₁ hgen₁ hsuppRefl₁)
      (canonicalObservablePiecesV3 huse₂ hsuppRun₂ hgen₂ hsuppRefl₂) := by
  exact canonicalVisiblePiecesV3_wellDefined hrununiq hrefluniq
    huse₁ hsuppRun₁ hgen₁ hsuppRefl₁ huse₂ hsuppRun₂ hgen₂ hsuppRefl₂

end Cpp
