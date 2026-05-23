import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Tail.ProofDemand

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail lifting

A tail result is lifted through `BigStepStmt.seqNormal`; tail divergence is
lifted through `BigStepStmtDiv.seqRight`.

This file depends only on the core route, continuation input, and proof demand.
Tail adequacy is not needed for this semantic lifting theorem.
-/

theorem step
    {Γ : TypeEnv} {σ σ1 σ2 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    {ctrl : CtrlResult}
    (tailStep : BigStepStmt σ1 t ctrl σ2) :
    BigStepStmt σ (.seq s t) ctrl σ2 := by
  exact BigStepStmt.seqNormal route.hstepLeft tailStep

theorem diverges
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (tailDiv : BigStepStmtDiv σ1 t) :
    BigStepStmtDiv σ (.seq s t) := by
  exact BigStepStmtDiv.seqRight route.hstepLeft tailDiv

theorem closeAndLiftFromContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (continuation : ContinuationInput route)
    (tailProof : ProofDemand route) :
    (∃ ctrl σ2, BigStepStmt σ (.seq s t) ctrl σ2) ∨
      BigStepStmtDiv σ (.seq s t) := by
  let dyn : StmtContinuationDynamicBoundary route.Θ σ1 t :=
    continuation.toDynamicBoundary
  match tailProof.close dyn with
  | Or.inl ⟨ctrl, σ2, hstep⟩ =>
      exact
        Or.inl
          ⟨ctrl, σ2,
            step
              (Γ := Γ) (σ := σ) (σ1 := σ1) (σ2 := σ2)
              (s := s) (t := t) (P := P) (route := route)
              (ctrl := ctrl)
              hstep⟩
  | Or.inr hdiv =>
      exact
        Or.inr
          (diverges
            (Γ := Γ) (σ := σ) (σ1 := σ1)
            (s := s) (t := t) (P := P) (route := route)
            hdiv)

theorem closeAndLift
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (pkg : Package route) :
    (∃ ctrl σ2, BigStepStmt σ (.seq s t) ctrl σ2) ∨
      BigStepStmtDiv σ (.seq s t) := by
  exact
    closeAndLiftFromContinuationAndProof
      (Γ := Γ) (σ := σ) (σ1 := σ1)
      (s := s) (t := t) (P := P) (route := route)
      pkg.continuation
      pkg.tailProof

end Tail
end Seq
end CompoundContinuation
end Cpp
