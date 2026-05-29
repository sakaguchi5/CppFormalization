import CppFormalization.Cpp2.Route.ContinuationRoute.Seq
import CppFormalization.Cpp2.Continuation.Compound.ReplayCore

namespace Cpp
namespace CompoundContinuation
namespace Seq

/-!
# Seq routes

The normal route is now the core selected `SeqHeadNormalRouteCoreCI`.
The older `SeqHeadNormalRouteCI` remains available as a legacy full route that
bundles tail static/adequacy payloads, but the compound-continuation contract
surface should not depend on that payload.

Non-tail exits are named separately because they do not enter the continuation
target.
-/

abbrev NormalRoute
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s} :=
  SeqHeadNormalRouteCoreCI Γ σ s t σ1 P

abbrev LegacyNormalRoute
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
