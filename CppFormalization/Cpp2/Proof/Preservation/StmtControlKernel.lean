import CppFormalization.Cpp2.Proof.Preservation.StmtControlRecursorCore
--import CppFormalization.Cpp2.Continuation.Boundary.LegacyTransport
import CppFormalization.Cpp2.Continuation.Boundary.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Cons
import CppFormalization.Cpp2.Proof.Preservation.StmtControlStateOnly

namespace Cpp

/-!
# Proof.Preservation.StmtControlKernel

Theorem-backed preservation kernel over compatibility derivations.

The old shell axioms are gone. The price is explicit: the kernel now requires
`WhileCtxProvider`, because the recursive `while` branches genuinely need the
extra local data encoded there.

The `seq normal` and block `cons normal` handlers no longer use the legacy
exact-tail projections directly.  They project the pre-world tail readiness and
then construct statement/block continuation dynamic boundaries.
The temporary constructors still use the legacy `ReadinessTransportNormalCore`
obligation internally.  This shifts the remaining ordinary-readiness debt from the
specialized exact-tail axiom to the general readiness-transport family.
-/

theorem stmt_control_preserves_scoped_typed_state_of_compatible
    (_mkWhileReentry : WhileReentryReadyProvider)
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ _hready
  exact
    stmt_control_preserves_scoped_typed_state_of_compatible_noReady
      hcomp hσ

theorem block_control_preserves_scoped_typed_state_of_compatible
    (_mkWhileReentry : WhileReentryReadyProvider)
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ _hready
  exact
    block_control_preserves_scoped_typed_state_of_compatible_noReady
      hcomp hσ

end Cpp
