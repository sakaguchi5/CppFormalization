import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.ReflectionFragmentV3

V3 external interface for the reflection/generation-side fragment.

Compared with V2, this restores explicit target-indexed applicability relations
for structural/profile certification, while keeping witness-producing outputs.
-/

structure VerifiedReflectionFragmentV3 where
  Meta : Type
  generates : Meta → CppStmt → Prop
  supportsStructural : Meta → TypeEnv → CppStmt → Prop
  supportsProfile : Meta → TypeEnv → CppStmt → Prop

  mkStructural :
    ∀ {m : Meta} {Γ : TypeEnv} {st : CppStmt},
      generates m st →
      supportsStructural m Γ st →
      BodyStructuralBoundary Γ st

  mkProfile :
    ∀ {m : Meta} {Γ : TypeEnv} {st : CppStmt},
      generates m st →
      supportsProfile m Γ st →
      BodyControlProfile Γ st

  mkCore :
    ∀ {m : Meta} {st : CppStmt},
      generates m st →
      CoreBigStepFragment st

end Cpp
