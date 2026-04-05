import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.External.ReflectionFragmentV3

namespace Cpp

/-!
# Closure.External.GlueV3

Stage 2A redesign:
- low-level glue no longer quantifies over an arbitrary profile,
- adequacy is required only over the canonical profile chosen by the
  reflection package,
- this matches both the mathematics and the intended C++ reading:
  control summary is certified output, not user-supplied input.
-/

structure VerifiedExternalGlueV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3) where
  compatible :
    F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

  mkAdequacy :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      (h_uses : F.uses n) →
      (h_runtime : F.supportsRuntime n Γ σ st) →
      (h_gen : R.generates m st) → -- 名前を付ける
      (h_refl : R.supportsReflection m Γ st) → -- 名前を付ける
      compatible n m Γ σ st →
      BodyAdequacyCI Γ σ st
        ((R.mkReflection (m := m) (Γ := Γ) (st := st) h_gen h_refl).profile)
end Cpp
