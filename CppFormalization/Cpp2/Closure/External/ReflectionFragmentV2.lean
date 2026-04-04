import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.ReflectionFragmentV2

V2 external interface: the reflection/generation-side fragment is responsible
for producing the structural boundary, the control profile, and core-fragment
membership for the generated statement.
-/

structure VerifiedReflectionFragmentV2 where
  Meta : Type
  generates : Meta → CppStmt → Prop

  mkStructural :
    ∀ {m : Meta} {Γ : TypeEnv} {st : CppStmt},
      generates m st → BodyStructuralBoundary Γ st

  mkProfile :
    ∀ {m : Meta} {Γ : TypeEnv} {st : CppStmt},
      generates m st → BodyControlProfile Γ st

  mkCore :
    ∀ {m : Meta} {st : CppStmt},
      generates m st → CoreBigStepFragment st

end Cpp
