import CppFormalization.Cpp2.Closure.Foundation.StateBoundary

namespace Cpp

/-!
# Closure.External.Interface

`reflective_std_closure_theorem` の外側にある責務を、最小限の interface に切り出す。

- `std` 側は BodyReady を立てる責任を持つ。
- `reflection` 側は対象 statement が core fragment に入る責任を持つ。
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

end Cpp
