import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Tail.ProofDemand

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail lifting

A block-tail result is lifted through `BigStepBlock.consNormal`; block-tail
divergence is lifted through `BigStepBlockDiv.consTail`.
-/

theorem step
    {Γ : TypeEnv} {σ σ1 σ2 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    {ctrl : CtrlResult}
    (tailStep : BigStepBlock σ1 tail ctrl σ2) :
    BigStepBlock σ (.cons head tail) ctrl σ2 := by
  exact BigStepBlock.consNormal route.hhead tailStep

theorem diverges
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (tailDiv : BigStepBlockDiv σ1 tail) :
    BigStepBlockDiv σ (.cons head tail) := by
  exact BigStepBlockDiv.consTail route.hhead tailDiv

theorem closeAndLiftFromContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (continuation : ContinuationInput route)
    (tailProof : ProofDemand route) :
    (∃ ctrl σ2, BigStepBlock σ (.cons head tail) ctrl σ2) ∨
      BigStepBlockDiv σ (.cons head tail) := by
  let dyn : BlockContinuationDynamicBoundary Γ σ1 tail :=
    continuation.toDynamicBoundary
  match tailProof.close dyn with
  | Or.inl ⟨ctrl, σ2, hstep⟩ =>
      exact
        Or.inl
          ⟨ctrl, σ2,
            step
              (Γ := Γ) (σ := σ) (σ1 := σ1) (σ2 := σ2)
              (head := head) (tail := tail) (route := route)
              (ctrl := ctrl)
              hstep⟩
  | Or.inr hdiv =>
      exact
        Or.inr
          (diverges
            (Γ := Γ) (σ := σ) (σ1 := σ1)
            (head := head) (tail := tail) (route := route)
            hdiv)

theorem closeAndLift
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (pkg : Package route) :
    (∃ ctrl σ2, BigStepBlock σ (.cons head tail) ctrl σ2) ∨
      BigStepBlockDiv σ (.cons head tail) := by
  exact
    closeAndLiftFromContinuationAndProof
      (Γ := Γ) (σ := σ) (σ1 := σ1)
      (head := head) (tail := tail) (route := route)
      pkg.continuation
      pkg.tailProof

end Tail
end Cons
end CompoundContinuation
end Cpp
