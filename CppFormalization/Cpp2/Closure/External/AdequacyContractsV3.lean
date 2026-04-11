import CppFormalization.Cpp2.Closure.External.AdequacyNormalV3
import CppFormalization.Cpp2.Closure.External.AdequacyReturnV3
import CppFormalization.Cpp2.Closure.External.GlueV3

namespace Cpp

/-!
# Closure.External.AdequacyContractsV3

Honest adequacy route built from explicit reflection-side semantic contracts.

Purpose:
- make the remaining lie location explicit:
  the unresolved external semantic content is exactly the pair of contracts
  `NormalCompatibilityV3` / `ReturnCompatibilityV3`;
- package those two contracts into the exact `BodyAdequacyCI` and
  `VerifiedExternalGlueV3` objects expected by the existing V3 route.
-/

/-- The exact pair of remaining reflection-side adequacy contracts. -/
structure CanonicalAdequacyContractsV3
    (R : VerifiedReflectionFragmentV3) : Prop where
  normal : NormalCompatibilityV3 R
  returned : ReturnCompatibilityV3 R

/-- Build the canonical adequacy object from the explicit contracts. -/
noncomputable def canonicalAdequacyV3_ofContracts
    {R : VerifiedReflectionFragmentV3}
    (H : CanonicalAdequacyContractsV3 R)
    {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    BodyAdequacyCI Γ σ st
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl) := by
  refine
    { normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep
    exact canonical_profile_normal_sound_v3_of_normalCompat H.normal hgen hrefl hstep
  · intro rv σ' hstep
    exact canonical_profile_return_sound_v3_of_returnCompat H.returned hgen hrefl hstep

/--
Build the honest canonical glue object from:
- a compatibility predicate, and
- the explicit pair of adequacy contracts.
-/
noncomputable def canonicalGlueV3_ofContracts
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R) :
    VerifiedExternalGlueV3 F R where
  compatible := Compat
  mkAdequacy := by
    intro n m Γ σ st huses hruntime hgen hrefl hcompat
    exact canonicalAdequacyV3_ofContracts H hgen hrefl

end Cpp
