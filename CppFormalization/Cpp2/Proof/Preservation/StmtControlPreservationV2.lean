import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernel

namespace Cpp

/-!
# Proof.Preservation.StmtControlPreservationV2

The strong theorem-backed route is now identical to the kernel route.
We keep this file only as a compatibility surface for the old V2 name.
-/

abbrev whileCompatHandlers_v2 := whileCompatHandlers_kernel

theorem stmt_control_preserves_scoped_typed_state_of_compatible_core
    (mkWhileCtx : WhileCtxProvider)
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' :=
  stmt_control_preserves_scoped_typed_state_of_compatible
    mkWhileCtx hcomp

end Cpp
