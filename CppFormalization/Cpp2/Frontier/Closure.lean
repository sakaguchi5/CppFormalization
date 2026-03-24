import CppFormalization.Cpp2.Frontier.SafetyAxioms

/-!
Closure theorems for verified standard and reflection fragments.
-/

namespace Cpp

structure VerifiedStdFragment where
  Name : Type
  uses : Name → Prop
  closedUnder : Name → CppStmt → Prop

structure VerifiedReflectionFragment where
  Meta : Type
  generates : Meta → CppStmt → Prop
  preserves : Meta → TypeEnv → State → CppStmt → Prop

axiom std_fragment_preserves_ideal_boundary
    {F : VerifiedStdFragment} {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.closedUnder n st →
    IdealAssumptions Γ σ st

axiom reflection_fragment_preserves_core_fragment
    {R : VerifiedReflectionFragment} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    R.generates m st →
    R.preserves m Γ σ st →
    CoreBigStepFragment st

theorem reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.closedUnder n st →
    R.generates m st →
    R.preserves m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hclosed hgen hpres
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_preserves_core_fragment hgen hpres
  have hassm : IdealAssumptions Γ σ st :=
    std_fragment_preserves_ideal_boundary huse hclosed
  exact ideal_no_stuck hfrag hassm

end Cpp
