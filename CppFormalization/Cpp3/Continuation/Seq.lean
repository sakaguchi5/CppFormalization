import CppFormalization.Cpp3.Continuation.Core

/-!
# CppFormalization.Cpp3.Continuation.Seq

Continuation surfaces for statement sequencing.

A sequence continuation consumes the target boundary produced by
`Stability.SeqTailStability`: after the head finishes normally, the tail boundary
at the head post-state is available.
-/

namespace Cpp3
namespace Continuation

/-- Continuation from a normally completed sequence head to its statement tail. -/
structure SeqTailContinuation
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  stability : Stability.SeqTailStability Γ Θ σ σ₁ head tail

namespace SeqTailContinuation

/-- The source boundary for the whole sequence. -/
def source
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailContinuation Γ Θ σ σ₁ head tail) :
    Boundary.StmtBoundary Γ σ (.seq head tail) :=
  h.stability.source

/-- The selected normal route through the sequence head. -/
def route
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailContinuation Γ Θ σ σ₁ head tail) :
    Semantics.SeqNormalRoute σ σ₁ head tail :=
  h.stability.target.route

/-- The complete target boundary package for the statement tail. -/
def target
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailContinuation Γ Θ σ σ₁ head tail) :
    Boundary.SeqTailBoundary Γ Θ σ σ₁ head tail :=
  h.stability.target

/-- The statement boundary consumed by the next execution step. -/
def tailBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailContinuation Γ Θ σ σ₁ head tail) :
    Boundary.StmtBoundary Θ σ₁ tail :=
  h.stability.target.tail

end SeqTailContinuation

end Continuation
end Cpp3
