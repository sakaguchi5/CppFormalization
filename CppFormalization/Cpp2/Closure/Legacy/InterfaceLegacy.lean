import CppFormalization.Cpp2.Closure.Foundation.StateBoundary

namespace Cpp.Legacy

/-!
# Closure.Legacy.InterfaceLegacy

第7段階で mainline から退避した old coarse external interface.
-/

structure VerifiedStdFragment where
  Name : Type
  uses : Name → Prop
  establishesBoundary : Name → TypeEnv → State → CppStmt → Prop

structure VerifiedReflectionFragment where
  Meta : Type
  generates : Meta → CppStmt → Prop

axiom std_fragment_establishes_body_ready
    {F : VerifiedStdFragment} {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesBoundary n Γ σ st →
    BodyReady Γ σ st

axiom reflection_fragment_generates_core
    {R : VerifiedReflectionFragment} {m : R.Meta} {st : CppStmt} :
    R.generates m st →
    CoreBigStepFragment st

end Cpp.Legacy
