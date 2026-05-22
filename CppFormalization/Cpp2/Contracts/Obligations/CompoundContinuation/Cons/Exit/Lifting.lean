import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Route

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Exit

/-!
# Cons non-tail exit lifting

If the head exits by break/continue/return or diverges, the block tail is not
entered.
-/

theorem blockStepOfHeadBreak
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadBreakRoute Γ σ σ1 head tail) :
    BigStepBlock σ (.cons head tail) .breakResult σ1 := by
  exact BigStepBlock.consBreak route.hhead

theorem blockStepOfHeadContinue
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadContinueRoute Γ σ σ1 head tail) :
    BigStepBlock σ (.cons head tail) .continueResult σ1 := by
  exact BigStepBlock.consContinue route.hhead

theorem blockStepOfHeadReturn
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {rv : Option Value}
    (route : HeadReturnRoute Γ σ σ1 head tail rv) :
    BigStepBlock σ (.cons head tail) (.returnResult rv) σ1 := by
  exact BigStepBlock.consReturn route.hhead

theorem blockDivOfHeadDiverges
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadDivergesRoute Γ σ head tail) :
    BigStepBlockDiv σ (.cons head tail) := by
  exact BigStepBlockDiv.consHere route.hheadDiv

end Exit
end Cons
end CompoundContinuation
end Cpp
