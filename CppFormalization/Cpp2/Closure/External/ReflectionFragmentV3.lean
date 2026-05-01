import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.ReflectionFragmentV3

Redesign:
- reflection returns `(structural, static, core)`;
- `entry/profile` are no longer independent external outputs;
- they are projections from the canonical static CI package.
-/

structure ReflectionPiecesV3 (Γ : TypeEnv) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  core : CoreBigStepFragment st

namespace ReflectionPiecesV3

def entry
    {Γ : TypeEnv} {st : CppStmt}
    (p : ReflectionPiecesV3 Γ st) :
    BodyEntryWitness Γ st :=
  p.static.root

def profile
    {Γ : TypeEnv} {st : CppStmt}
    (p : ReflectionPiecesV3 Γ st) :
    BodyControlProfile Γ st :=
  p.static.profile

end ReflectionPiecesV3

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
