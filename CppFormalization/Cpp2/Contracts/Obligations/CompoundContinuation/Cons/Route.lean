import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.ReplayCore

namespace Cpp
namespace CompoundContinuation
namespace Cons

/-!
# Cons routes

A cons route is a selected operational route through an already-open/current
block tail `s :: ss`.
-/

structure TailStaticAdequacyPayload
    (Γ : TypeEnv) (σ1 : State) (ss : StmtBlock) : Type where
  static : BlockBodyStaticBoundaryCI Γ ss
  adequacy : BlockBodyAdequacyCI Γ σ1 ss static.profile

structure HeadNormalRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hhead : BigStepStmt σ head .normal σ1
  tailPayload : TailStaticAdequacyPayload Γ σ1 tail

structure HeadBreakRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hhead : BigStepStmt σ head .breakResult σ1

structure HeadContinueRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hhead : BigStepStmt σ head .continueResult σ1

structure HeadReturnRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) (rv : Option Value) : Type where
  hhead : BigStepStmt σ head (.returnResult rv) σ1

structure HeadDivergesRoute
    (Γ : TypeEnv) (σ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hheadDiv : BigStepStmtDiv σ head

end Cons
end CompoundContinuation
end Cpp
