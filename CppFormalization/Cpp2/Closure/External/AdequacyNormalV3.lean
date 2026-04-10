import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.External.AdequacyNormalV3

Dedicated workbench for the normal-side adequacy kernel.

Purpose:
- isolate the exact normal-side target used by `BodyAdequacyCI.normalSound`,
- keep a named staging theorem for replacing the current axiom later,
- let downstream files talk about the normal kernel without reopening the whole
  adequacy packaging story.

Current status:
- this file is intentionally conservative,
- it re-expresses the normal kernel target in a dedicated module,
- and it currently derives the staging theorem from the existing kernel axiom
  in `AdequacyKernelV3`.

Once the real proof is ready, replace the body of
`canonical_profile_normal_sound_kernel_v3` directly.
-/

/-- The exact normal-side target for the canonical V3 profile. -/
abbrev CanonicalNormalGoalV3
    {R : VerifiedReflectionFragmentV3}
    {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) : Prop :=
  ∀ {σ' : State},
    BigStepStmt σ st .normal σ' →
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.normalOut = some out

/--
Staging theorem for the normal-side kernel.

This has the exact same semantic content as the current normal-side kernel axiom,
but lives in its own file so that the eventual proof can be developed and audited
independently.
-/
theorem canonical_profile_normal_sound_kernel_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st)
    {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.normalOut = some out := by
  exact
    canonical_profile_normal_sound_v3
      (F := F) (R := R) Compat
      huses hruntime hgen hrefl hcompat hstep

/-- Bundled normal-side kernel statement. -/
theorem canonical_profile_normal_goal_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    CanonicalNormalGoalV3 (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st) hgen hrefl := by
  intro σ' hstep
  exact
    canonical_profile_normal_sound_kernel_v3
      (F := F) (R := R) Compat
      huses hruntime hgen hrefl hcompat hstep

end Cpp
