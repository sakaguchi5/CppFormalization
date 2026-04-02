import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.StateBoundary

namespace Cpp

/-!
# Closure.External.InterfaceCI

第6段階の external adapter interface.

方針:
- `std` / runtime 側は dynamic boundary を供給する。
- reflection 側は structural boundary と control profile を供給する。
- 最終的な assembled boundary (`ClosureV2.BodyClosureBoundaryCI`) は
  adapter theorem でまとめて得る。
- old `Interface` は legacy surface として残し、こちらが V2 surface になる。
-/

structure VerifiedStdFragmentCI where
  Name : Type
  uses : Name → Prop
  establishesDynamic : Name → TypeEnv → State → CppStmt → Prop

structure VerifiedReflectionFragmentCI where
  Meta : Type
  generates : Meta → CppStmt → Prop
  establishesStructural : Meta → TypeEnv → CppStmt → Prop
  establishesProfile : Meta → TypeEnv → CppStmt → Prop

axiom std_fragment_establishes_dynamic_boundary_v2
    {F : VerifiedStdFragmentCI} {n : F.Name}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    ClosureV2.BodyDynamicBoundary Γ σ st

axiom reflection_fragment_establishes_structural_boundary_v2
    {R : VerifiedReflectionFragmentCI} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesStructural m Γ st →
    ClosureV2.BodyStructuralBoundary Γ st

axiom reflection_fragment_establishes_control_profile_v2
    {R : VerifiedReflectionFragmentCI} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesProfile m Γ st →
    ClosureV2.BodyControlProfile Γ st

axiom reflection_fragment_generates_core_v2
    {R : VerifiedReflectionFragmentCI} {m : R.Meta} {st : CppStmt} :
    R.generates m st →
    CoreBigStepFragment st

/--
External adapter theorem.

注意:
- adequacy の構成は external 利用者に露出しない。
- 外側の responsibility split を保ったまま assembled boundary を返す。
-/
axiom fragments_establish_body_closure_boundary_v2
    {F : VerifiedStdFragmentCI} {R : VerifiedReflectionFragmentCI}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    ClosureV2.BodyClosureBoundaryCI Γ σ st

end Cpp
