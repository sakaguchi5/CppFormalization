import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.External.AdequacyNormalV3

Normal-side *semantic contract* for the honest adequacy route.

Key point:
- this file does **not** pretend that normal profile soundness is derivable from
  the current generic kernel axioms alone;
- instead it exposes the real missing contract explicitly.

Meaning:
once reflection chooses a canonical profile for a generated statement,
every actual normal execution of that statement is already represented by the
canonical normal summary.
-/

/-- Exact bundled normal-side target for the canonical V3 profile. -/
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
Pure reflection-side semantic contract for normal completion.

This is the honest place where the remaining normal-side adequacy assumption
lives.
-/
structure NormalCompatibilityV3
    (R : VerifiedReflectionFragmentV3) : Prop where
  normalSound :
    ∀ {m : R.Meta}
      {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (hgen : R.generates m st)
      (hrefl : R.supportsReflection m Γ st)
      {σ' : State},
      BigStepStmt σ st .normal σ' →
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
        (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.normalOut = some out

/-- Pointwise normal-side soundness from the explicit contract. -/
theorem canonical_profile_normal_sound_v3_of_normalCompat
    {R : VerifiedReflectionFragmentV3}
    (H : NormalCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.normalOut = some out :=
  H.normalSound hgen hrefl hstep

/-- Bundled normal-side soundness from the explicit contract. -/
theorem canonical_profile_normal_goal_v3_of_normalCompat
    {R : VerifiedReflectionFragmentV3}
    (H : NormalCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    CanonicalNormalGoalV3 (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st) hgen hrefl := by
  intro σ' hstep
  exact canonical_profile_normal_sound_v3_of_normalCompat H hgen hrefl hstep

/--
Compatibility-wrapper theorem name kept as a staging surface.

This theorem now says exactly what it should say:
the result follows from the explicit reflection-side normal contract,
not from hidden generic assumptions.
-/
theorem canonical_profile_normal_sound_kernel_v3
    {R : VerifiedReflectionFragmentV3}
    (H : NormalCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.normalOut = some out := by
  exact canonical_profile_normal_sound_v3_of_normalCompat H hgen hrefl hstep

/-- Bundled wrapper theorem name kept for downstream migration. -/
theorem canonical_profile_normal_goal_v3
    {R : VerifiedReflectionFragmentV3}
    (H : NormalCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    CanonicalNormalGoalV3 (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st) hgen hrefl := by
  exact canonical_profile_normal_goal_v3_of_normalCompat H hgen hrefl

end Cpp
