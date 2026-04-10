import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.External.AdequacyReturnV3

Dedicated workbench for the return-side adequacy kernel.

Interpretation after simplification:
- `ReturnCompatibilityV3` is no longer a mixed std/glue/reflection notion.
- It is now a *pure reflection-side semantic contract*.
- Concretely, it says:
  once a reflection package chooses a canonical profile for a generated statement,
  every actual return execution of that statement is already accounted for by
  that canonical profile.

This is mathematically stronger and cleaner than the earlier version:
the contract no longer pretends to depend on runtime-side compatibility inputs
if those inputs never actually appear in the actual target statement.
-/

/-- The exact bundled return-side target for the canonical V3 profile. -/
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

No std-side fragment, compatibility predicate, or runtime-side support witness
appears here anymore, because none of them survived into the actual target
statement.
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

/--
Main theorem from the explicit return-compatibility contract to the exact
canonical return-soundness statement.
-/
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

/-- Bundled return-side target obtained from `ReturnCompatibilityV3`. -/
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

/--
Compatibility wrapper name kept as a staging surface.

This theorem now makes the real dependency explicit:
what matters is the reflection-side `ReturnCompatibilityV3` contract.
-/
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

/-- Bundled return-side kernel statement via the explicit compatibility structure. -/
theorem canonical_profile_return_goal_v3
    {R : VerifiedReflectionFragmentV3}
    (H : ReturnCompatibilityV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    CanonicalReturnGoalV3 (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st) hgen hrefl := by
  exact canonical_profile_return_goal_v3_of_returnCompat H hgen hrefl

/--
Conservative bridge from the current generic kernel axiom.

This lets downstream code migrate immediately, while making the stronger and
cleaner reflection-side contract explicit.
-/
theorem returnCompatibilityV3_of_kernelAxiom
    {F : VerifiedStdFragmentV3}
    {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name}
    (huses : F.uses n)
    (defaultRuntime :
      ∀ {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
        R.generates m st →
        R.supportsReflection m Γ st →
        F.supportsRuntime n Γ σ st)
    (defaultCompat :
      ∀ {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
        R.generates m st →
        R.supportsReflection m Γ st →
        Compat n m Γ σ st) :
    ReturnCompatibilityV3 R := by
  refine ⟨?_⟩
  intro m Γ σ st hgen hrefl rv σ' hstep
  exact
    canonical_profile_return_sound_v3
      (F := F) (R := R) Compat
      huses
      (defaultRuntime hgen hrefl)
      hgen
      hrefl
      (defaultCompat hgen hrefl)
      hstep

end Cpp
