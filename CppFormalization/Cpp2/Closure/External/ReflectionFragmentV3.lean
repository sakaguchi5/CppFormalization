import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.ReflectionFragmentV3

Stage 2A redesign:
- the reflection side returns one target-indexed package,
- structural boundary, control profile, and core membership are chosen together,
- this removes the old split between `supportsStructural` and `supportsProfile`
  that caused coherence to be lost in the glue route.
-/

structure ReflectionPiecesV3 (Γ : TypeEnv) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  entry : BodyEntryWitness Γ st
  profile : BodyControlProfile Γ st
  core : CoreBigStepFragment st

structure VerifiedReflectionFragmentV3 where
  Meta : Type
  generates : Meta → CppStmt → Prop
  supportsReflection : Meta → TypeEnv → CppStmt → Prop
  mkReflection :
    ∀ {m : Meta} {Γ : TypeEnv} {st : CppStmt},
      generates m st →
      supportsReflection m Γ st →
      ReflectionPiecesV3 Γ st

end Cpp
