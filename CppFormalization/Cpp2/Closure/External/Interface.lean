import CppFormalization.Cpp2.Closure.External.InterfaceCI

namespace Cpp

/-!
# Closure.External.Interface

Mainline external interface after the Stage 7 switch.

方針:
- canonical external interface は V2 adapter (`InterfaceCI`) を thin wrapper として採用する。
- old coarse `BodyReady` 直結 interface は `Closure.Legacy.InterfaceLegacy` へ退避済み。
- profile / assembled boundary を返す wrapper は proposition ではなく data を返すので
  `noncomputable abbrev` を使っている。
-/

abbrev VerifiedStdFragment := VerifiedStdFragmentCI
abbrev VerifiedReflectionFragment := VerifiedReflectionFragmentCI

abbrev std_fragment_establishes_dynamic_boundary
    {F : VerifiedStdFragment} {n : F.Name}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    ClosureV2.BodyDynamicBoundary Γ σ st :=
  std_fragment_establishes_dynamic_boundary_v2

abbrev reflection_fragment_establishes_structural_boundary
    {R : VerifiedReflectionFragment} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesStructural m Γ st →
    ClosureV2.BodyStructuralBoundary Γ st :=
  reflection_fragment_establishes_structural_boundary_v2

noncomputable abbrev reflection_fragment_establishes_control_profile
    {R : VerifiedReflectionFragment} {m : R.Meta}
    {Γ : TypeEnv} {st : CppStmt} :
    R.generates m st →
    R.establishesProfile m Γ st →
    ClosureV2.BodyControlProfile Γ st :=
  reflection_fragment_establishes_control_profile_v2

abbrev reflection_fragment_generates_core
    {R : VerifiedReflectionFragment} {m : R.Meta} {st : CppStmt} :
    R.generates m st →
    CoreBigStepFragment st :=
  reflection_fragment_generates_core_v2

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
