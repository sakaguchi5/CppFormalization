import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/--
Future-use certificate carrier for a remaining statement `st` after some
preceding normal step has finished.

Current mainline 2a intentionally uses the Prop-level alias
`SeqResidualBoundary` below instead of this structure, because the typing
judgment packaged here lives in `Prop`. Keeping the public residual boundary
Prop-valued avoids large-elimination friction while the transport kernel is
still being reorganized.
-/
structure StmtResidualBoundary
    (Δ : TypeEnv) (σ' : State) (st : CppStmt) where
  residualEnv : TypeEnv
  typing : HasTypeStmtCI .normalK residualEnv st Δ
  state : ScopedTypedStateConcrete residualEnv σ'
  ready : StmtReadyConcrete residualEnv σ' st

/--
Future-use certificate carrier for a remaining block tail `ss` after the head
statement has finished normally.

Current mainline 2a intentionally uses the Prop-level alias
`ConsResidualBoundary` below instead of this structure, because the typing
judgment packaged here lives in `Prop`. Keeping the public residual boundary
Prop-valued avoids large-elimination friction while the transport kernel is
still being reorganized.
-/
structure BlockResidualBoundary
    (Δ : TypeEnv) (σ' : State) (ss : StmtBlock) where
  residualEnv : TypeEnv
  typing : HasTypeBlockCI .normalK residualEnv ss Δ
  state : ScopedTypedStateConcrete residualEnv σ'
  ready : BlockReadyConcrete residualEnv σ' ss

/--
Mainline residual boundary for a remaining statement.

This is intentionally Prop-valued for now. The future structure
`StmtResidualBoundary` above is kept as a certificate target once the transport
layer is reorganized enough to use packaged witnesses directly.
-/
def SeqResidualBoundary
    (Δ : TypeEnv) (σ' : State) (t : CppStmt) : Prop :=
  ∃ Θ,
    HasTypeStmtCI .normalK Θ t Δ ∧
    ScopedTypedStateConcrete Θ σ' ∧
    StmtReadyConcrete Θ σ' t

/--
Mainline residual boundary for a remaining block tail.

This is intentionally Prop-valued for now. The future structure
`BlockResidualBoundary` above is kept as a certificate target once the
transport layer is reorganized enough to use packaged witnesses directly.
-/
def ConsResidualBoundary
    (Δ : TypeEnv) (σ' : State) (ss : StmtBlock) : Prop :=
  ∃ Ξ,
    HasTypeBlockCI .normalK Ξ ss Δ ∧
    ScopedTypedStateConcrete Ξ σ' ∧
    BlockReadyConcrete Ξ σ' ss

end Cpp
