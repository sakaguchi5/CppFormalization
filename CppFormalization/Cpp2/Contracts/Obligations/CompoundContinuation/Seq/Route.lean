import CppFormalization.Cpp2.Continuation.Route.Seq
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.ReplayCore

namespace Cpp
namespace CompoundContinuation
namespace Seq

/-!
# Seq routes

The normal route is the existing selected `SeqHeadNormalRouteCI`.  Non-tail
exits are named separately because they do not enter the continuation target.
-/

abbrev NormalRoute
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s} :=
  SeqHeadNormalRouteCI Γ σ s t σ1 P

structure BreakRoute
    (Γ : TypeEnv) (σ σ1 : State) (s t : CppStmt) : Type where
  hleft : BigStepStmt σ s .breakResult σ1

structure ContinueRoute
    (Γ : TypeEnv) (σ σ1 : State) (s t : CppStmt) : Type where
  hleft : BigStepStmt σ s .continueResult σ1

structure ReturnRoute
    (Γ : TypeEnv) (σ σ1 : State) (s t : CppStmt) (rv : Option Value) : Type where
  hleft : BigStepStmt σ s (.returnResult rv) σ1

structure DivergesRoute
    (Γ : TypeEnv) (σ : State) (s t : CppStmt) : Type where
  hleftDiv : BigStepStmtDiv σ s

end Seq
end CompoundContinuation
end Cpp
