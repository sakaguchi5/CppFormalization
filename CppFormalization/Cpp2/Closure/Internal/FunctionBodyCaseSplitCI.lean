import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

abbrev FunctionBodyClosureResult (σ : State) (st : CppStmt) : Prop :=
  (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

structure SeqLeftClosureScaffoldCI
    (Γ : TypeEnv) (σ : State) (s : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ s
  entry : BodyEntryWitness Γ s
  profile : BodyControlProfile Γ s
  adequacy : BodyAdequacyCI Γ σ s profile

structure SeqTailClosureScaffoldCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  structural : BodyStructuralBoundary Θ t
  entry : BodyEntryWitness Θ t
  profile : BodyControlProfile Θ t
  adequacy : BodyAdequacyCI Θ σ1 t profile

axiom seq_left_closure_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    SeqLeftClosureScaffoldCI Γ σ s

axiom seq_tail_closure_scaffold_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      SeqTailClosureScaffoldCI Θ σ1 t

def seq_left_dynamic_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyDynamicBoundary Γ σ s :=
  { state := hentry.dynamic.state
    safe := seq_ready_left hentry.dynamic.safe }

noncomputable def seq_left_closure_boundary_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyClosureBoundaryCI Γ σ s := by
  let hs := seq_left_closure_scaffold_ci_of_entry hentry
  let hd := seq_left_dynamic_boundary_of_entry hentry
  sorry
  --exact mkBodyClosureBoundaryCI hs.structural hs.entry hs.profile hd hs.adequacy

noncomputable def seq_tail_closure_boundary_ci_of_left_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      BodyClosureBoundaryCI Θ σ1 t := by
  intro Θ σ1 htyLeft hstepLeft
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      mkWhileReentry htyLeft hentry.dynamic.state hreadyLeft hstepLeft
  have hreadyRight : StmtReadyConcrete Θ σ1 t :=
    seq_ready_right_after_left_normal htyLeft hσ1 hentry.dynamic.safe hstepLeft
  let hs := seq_tail_closure_scaffold_ci_of_left_normal hentry htyLeft hstepLeft
  let hd : BodyDynamicBoundary Θ σ1 t :=
    { state := hσ1
      safe := hreadyRight }
  sorry
  --exact mkBodyClosureBoundaryCI hs.structural hs.entry hs.profile hd hs.adequacy

axiom seq_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t)

axiom ite_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t))
    (thenClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyClosureBoundaryCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t)

theorem seq_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hleftBoundary => leftClosure hleftBoundary.toBodyReadyCI)
      (fun hty hstep => (tailBoundary hty hstep).toClosureBoundary)
      (fun hty hstep htailBoundary =>
        tailClosure hty hstep htailBoundary.toBodyReadyCI)

theorem ite_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.ite c s t))
    (thenClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyReadyCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  exact
    ite_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hthenBoundary => thenClosure hthenBoundary.toBodyReadyCI)
      (fun helseBoundary => elseClosure helseBoundary.toBodyReadyCI)

end Cpp
