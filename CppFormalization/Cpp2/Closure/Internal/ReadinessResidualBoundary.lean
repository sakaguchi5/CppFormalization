import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/--
Residual entry boundary for a remaining statement `st` after some preceding
normal step has finished.
-/
structure StmtResidualBoundary
    (Δ : TypeEnv) (σ' : State) (st : CppStmt) where
  residualEnv : TypeEnv
  typing : HasTypeStmtCI .normalK residualEnv st Δ
  state : ScopedTypedStateConcrete residualEnv σ'
  ready : StmtReadyConcrete residualEnv σ' st

/--
Residual entry boundary for a remaining block tail `ss` after the head statement
has finished normally.
-/
structure BlockResidualBoundary
    (Δ : TypeEnv) (σ' : State) (ss : StmtBlock) where
  residualEnv : TypeEnv
  typing : HasTypeBlockCI .normalK residualEnv ss Δ
  state : ScopedTypedStateConcrete residualEnv σ'
  ready : BlockReadyConcrete residualEnv σ' ss

def SeqResidualBoundary
    (Δ : TypeEnv) (σ' : State) (t : CppStmt) : Prop :=
  ∃ Θ,
    HasTypeStmtCI .normalK Θ t Δ ∧
    ScopedTypedStateConcrete Θ σ' ∧
    StmtReadyConcrete Θ σ' t

def ConsResidualBoundary
    (Δ : TypeEnv) (σ' : State) (ss : StmtBlock) : Prop :=
  ∃ Ξ,
    HasTypeBlockCI .normalK Ξ ss Δ ∧
    ScopedTypedStateConcrete Ξ σ' ∧
    BlockReadyConcrete Ξ σ' ss

end Cpp
