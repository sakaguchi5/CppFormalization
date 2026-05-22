import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Route

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Exit

/-!
# Seq non-tail exit lifting

If the left statement exits by break/continue/return or diverges, the tail is not
entered.
-/

theorem stepOfLeftBreak
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (route : BreakRoute Γ σ σ1 s t) :
    BigStepStmt σ (.seq s t) .breakResult σ1 := by
  exact BigStepStmt.seqBreak route.hleft

theorem stepOfLeftContinue
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (route : ContinueRoute Γ σ σ1 s t) :
    BigStepStmt σ (.seq s t) .continueResult σ1 := by
  exact BigStepStmt.seqContinue route.hleft

theorem stepOfLeftReturn
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt} {rv : Option Value}
    (route : ReturnRoute Γ σ σ1 s t rv) :
    BigStepStmt σ (.seq s t) (.returnResult rv) σ1 := by
  exact BigStepStmt.seqReturn route.hleft

theorem divOfLeftDiverges
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (route : DivergesRoute Γ σ s t) :
    BigStepStmtDiv σ (.seq s t) := by
  exact BigStepStmtDiv.seqLeft route.hleftDiv

end Exit
end Seq
end CompoundContinuation
end Cpp
