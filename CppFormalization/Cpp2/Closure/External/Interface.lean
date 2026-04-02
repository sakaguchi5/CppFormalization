import CppFormalization.Cpp2.Closure.External.InterfaceCI

namespace Cpp

/-!
# Closure.External.Interface

第7段階の mainline external interface.

方針:
- canonical external interface は V2 adapter (`InterfaceCI`) に切り替える。
- old coarse `BodyReady` 直結 interface は legacy へ退避する。
-/

abbrev VerifiedStdFragment := VerifiedStdFragmentCI
abbrev VerifiedReflectionFragment := VerifiedReflectionFragmentCI

theorem std_fragment_establishes_dynamic_boundary
    {F : VerifiedStdFragment} {n : F.Name}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    ClosureV2.BodyDynamicBoundary Γ σ st := by
  intro huse hdyn
  exact std_fragment_establishes_dynamic_boundary_v2 huse hdyn

theorem reflection_fragment_establishes_structural_boundary
    {R : VerifiedReflectionFragment} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesStructural m Γ st →
    ClosureV2.BodyStructuralBoundary Γ st := by
  intro hgen hstruct
  exact reflection_fragment_establishes_structural_boundary_v2 hgen hstruct

noncomputable abbrev reflection_fragment_establishes_control_profile
    {R : VerifiedReflectionFragment} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesProfile m Γ st →
    ClosureV2.BodyControlProfile Γ st :=
  reflection_fragment_establishes_control_profile_v2

theorem reflection_fragment_generates_core
    {R : VerifiedReflectionFragment} {m : R.Meta} {st : CppStmt} :
    R.generates m st →
    CoreBigStepFragment st := by
  intro hgen
  exact reflection_fragment_generates_core_v2 hgen

noncomputable abbrev fragments_establish_body_closure_boundary
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    ClosureV2.BodyClosureBoundaryCI Γ σ st :=
  fragments_establish_body_closure_boundary_v2

end Cpp
