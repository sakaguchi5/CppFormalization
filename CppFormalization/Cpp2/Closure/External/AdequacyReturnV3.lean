import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.External.AdequacyReturnV3

Return-side *semantic contract* for the honest adequacy route.

Meaning:
once reflection chooses a canonical profile for a generated statement,
every actual return execution of that statement is already represented by the
canonical return summary.
-/

/-- Exact bundled return-side target for the canonical V3 profile. -/
abbrev CanonicalReturnGoalV3
    {R : VerifiedReflectionFragmentV3}
    {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) : Prop :=
  ∀ {rv : Option Value} {σ' : State},
    BigStepStmt σ st (.returnResult rv) σ' →
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out

/--
Pure reflection-side semantic contract for return completion.
-/
structure ReturnCompatibilityV3
    (R : VerifiedReflectionFragmentV3) : Prop where
  returnSound :
    ∀ {m : R.Meta}
      {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (hgen : R.generates m st)
      (hrefl : R.supportsReflection m Γ st)
      {rv : Option Value} {σ' : State},
      BigStepStmt σ st (.returnResult rv) σ' →
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
        (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out

/-- Pointwise return-side soundness from the explicit contract. -/
theorem canonical_profile_return_sound_v3_of_returnCompat
    {R : VerifiedReflectionFragmentV3}
    (H : ReturnCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ st (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out :=
  H.returnSound hgen hrefl hstep

/-- Bundled return-side soundness from the explicit contract. -/
theorem canonical_profile_return_goal_v3_of_returnCompat
    {R : VerifiedReflectionFragmentV3}
    (H : ReturnCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    CanonicalReturnGoalV3 (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st) hgen hrefl := by
  intro rv σ' hstep
  exact canonical_profile_return_sound_v3_of_returnCompat H hgen hrefl hstep

/-- Compatibility-wrapper theorem name kept as a staging surface. -/
theorem canonical_profile_return_sound_kernel_v3
    {R : VerifiedReflectionFragmentV3}
    (H : ReturnCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ st (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out := by
  exact canonical_profile_return_sound_v3_of_returnCompat H hgen hrefl hstep

/-- Bundled wrapper theorem name kept for downstream migration. -/
theorem canonical_profile_return_goal_v3
    {R : VerifiedReflectionFragmentV3}
    (H : ReturnCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    CanonicalReturnGoalV3 (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st) hgen hrefl := by
  exact canonical_profile_return_goal_v3_of_returnCompat H hgen hrefl

end Cpp
