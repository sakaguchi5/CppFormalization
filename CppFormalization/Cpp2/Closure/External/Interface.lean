import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

structure VerifiedStdFragment where
  Name : Type
  uses : Name → Prop
  establishesDynamic : Name → TypeEnv → State → CppStmt → Prop

structure VerifiedReflectionFragment where
  Meta : Type
  generates : Meta → CppStmt → Prop
  establishesStructural : Meta → TypeEnv → CppStmt → Prop
  establishesProfile : Meta → TypeEnv → CppStmt → Prop

axiom std_fragment_establishes_dynamic_boundary
    {F : VerifiedStdFragment} {n : F.Name}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    BodyDynamicBoundary Γ σ st

axiom reflection_fragment_establishes_structural_boundary
    {R : VerifiedReflectionFragment} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesStructural m Γ st →
    BodyStructuralBoundary Γ st

axiom reflection_fragment_establishes_control_profile
    {R : VerifiedReflectionFragment} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesProfile m Γ st →
    BodyControlProfile Γ st

axiom reflection_fragment_generates_core
    {R : VerifiedReflectionFragment} {m : R.Meta} {st : CppStmt} :
    R.generates m st →
    CoreBigStepFragment st

axiom fragments_establish_body_closure_boundary
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    BodyClosureBoundaryCI Γ σ st

end Cpp
