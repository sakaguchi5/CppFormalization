import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.External.AdequacyReturnV3

Dedicated workbench for the return-side adequacy kernel in the V3 route.

Purpose:
- isolate the return channel from the normal channel,
- give the return half of `BodyAdequacyCI` its own named theorem surface,
- make it easy to later replace the kernel axiom by a real proof without
  changing the rest of the V3 external assembly route.

Current role:
- this file is a thin wrapper around `canonical_profile_return_sound_v3` from
  `AdequacyKernelV3`.
-/

section ReturnKernel

/--
Return-side kernel statement for the canonical profile chosen by the V3
reflection package.

This is the exact return-channel obligation required by the `returnSound`
field of `BodyAdequacyCI`.
-/
theorem canonical_profile_return_sound_kernel_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ st (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out := by
  exact
    canonical_profile_return_sound_v3
      (F := F) (R := R) Compat
      huses hruntime hgen hrefl hcompat hstep

end ReturnKernel

section PackagingSanity

/--
Sanity wrapper: the packaged canonical adequacy witness exposes the same
return-side statement as the dedicated return kernel theorem.
-/
theorem canonicalAdequacyV3_returnSound
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ st (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out := by
  exact
    (canonicalAdequacyV3
      (F := F) (R := R) Compat
      huses hruntime hgen hrefl hcompat).returnSound hstep

end PackagingSanity

end Cpp
