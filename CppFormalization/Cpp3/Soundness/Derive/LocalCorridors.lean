import CppFormalization.Cpp3.Soundness.Instantiate.Easy

/-!
# CppFormalization.Cpp3.Soundness.Derive.LocalCorridors

Concrete construction layer for the local-control corridor theorem bundle.

`Soundness.Instantiate.Easy` introduced the public C++-facing local-control
corridor interfaces consumed by `StepLoopFinal`.  This file moves one step lower:
it describes how those corridors are obtained from the already existing
Boundary/Stability/Continuation/SafetyFragment/Semantics vocabulary.

The important separation is:

* `Instantiate.Easy` says which local corridors the final soundness engine needs;
* this file says that those corridors are constructed from concrete stability /
  entry / backedge construction theorems, not from old Soundness providers.

No old provider-shaped field appears in the construction bundle below.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LocalCorridors

/-- Lower-layer construction theorem for the sequence-tail stability package.

C++ reading: after a sequence head has completed normally, the selected tail
boundary is available at the head post-state, with the required footprint
preservation surface recorded in `Stability.SeqTailStability`. -/
structure SeqTailStabilityConstructionTheorem : Type where
  stability :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt},
      Boundary.StmtBoundary Γ σ (.seq head tail) →
      Semantics.SeqNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          Stability.SeqTailStability Γ Θ σ σ₁ head tail

/-- Convert a concrete sequence-tail stability theorem into the Easy corridor theorem. -/
def seqExecutionCorridorTheorem_of_stability
    (C : SeqTailStabilityConstructionTheorem) :
    Instantiate.Easy.SeqExecutionCorridorTheorem where
  corridor := by
    intro Γ σ σ₁ head tail boundary route
    rcases C.stability boundary route with ⟨Θ, stability⟩
    exact ⟨Θ, { stability := stability }⟩

/-- Lower-layer construction theorem for the block-tail stability package.

C++ reading: after a block head has completed normally, the remaining block body
is available in the post-state and under the correct tail environment. -/
structure BlockTailStabilityConstructionTheorem : Type where
  stability :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock},
      Boundary.BlockBoundary Γ σ (.cons head tail) →
      Semantics.BlockConsNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          Stability.BlockTailStability Γ Θ σ σ₁ head tail

/-- Convert a concrete block-tail stability theorem into the Easy corridor theorem. -/
def blockTailExecutionCorridorTheorem_of_stability
    (C : BlockTailStabilityConstructionTheorem) :
    Instantiate.Easy.BlockTailExecutionCorridorTheorem where
  corridor := by
    intro Γ σ σ₁ head tail boundary route
    rcases C.stability boundary route with ⟨Θ, stability⟩
    exact ⟨Θ, { stability := stability }⟩

/-- Lower-layer construction theorem for selected-branch stability.

C++ reading: evaluating the condition selects exactly one branch, and the boundary
for that selected branch is available at the condition post-state. -/
structure SelectedBranchStabilityConstructionTheorem : Type where
  select :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
        (Σ Γc : TypeEnv,
          Σ σc : State,
            Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch
              Semantics.BranchSide.thenBranch) ⊕
        (Σ Γc : TypeEnv,
          Σ σc : State,
            Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch
              Semantics.BranchSide.elseBranch)

/-- Convert selected-branch stability into the Easy selected-branch corridor theorem. -/
def selectedBranchCorridorTheorem_of_stability
    (C : SelectedBranchStabilityConstructionTheorem) :
    Instantiate.Easy.SelectedBranchCorridorTheorem where
  select := by
    intro Γ σ cond thenBranch elseBranch boundary
    cases C.select boundary with
    | inl selected =>
        rcases selected with ⟨Γc, σc, stability⟩
        exact Sum.inl ⟨Γc, σc, { stability := stability }⟩
    | inr selected =>
        rcases selected with ⟨Γc, σc, stability⟩
        exact Sum.inr ⟨Γc, σc, { stability := stability }⟩

/-- Lower-layer construction theorem for entering the while body after a true guard.

C++ reading: if the loop guard evaluates to true, the body is an executable
program point at the guard post-state.  The boundary itself contains the body
static/effect/safety surface; Soundness only consumes the resulting statement
boundary. -/
structure LoopBodyEntryBoundaryConstructionTheorem : Type where
  bodyBoundary :
    ∀ {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
        Boundary.StmtBoundary Γc σc body

/-- Convert while-body entry construction into the Easy loop-body corridor theorem. -/
def loopBodyEntryCorridorTheorem_of_boundary
    (C : LoopBodyEntryBoundaryConstructionTheorem) :
    Instantiate.Easy.LoopBodyEntryCorridorTheorem where
  corridor := by
    intro Γ Γc σ σc cond body boundary condition condTrue
    exact {
      source := boundary
      condition := condition
      condTrue := condTrue
      bodyBoundary := C.bodyBoundary boundary condition condTrue
    }

/-- Concrete lower-layer witness for a while normal/continue backedge.

C++ reading: after the body finishes by `normal` or `continue`, the loop can
re-enter the guard at `σreentry`; the reentry boundary and the visible reentry
certificate are carried explicitly. -/
structure LoopBackedgeConstructionWitness
    (Γ Γc : TypeEnv) (σ σreentry : State) (cond : CppCond) (body : CppStmt)
    (Reentry : Prop) : Type where
  stability : Stability.WhileBoundaryStability Γ Γc σ cond body
  reentryEq : Stability.WhileBoundaryStability.routePostState stability = σreentry
  reentryBoundary : Boundary.StmtBoundary Γ σreentry (.whileStmt cond body)
  certificate : Continuation.ContinuationCertificate Reentry

namespace LoopBackedgeConstructionWitness

/-- Convert the lower-layer backedge witness into the Easy backedge corridor. -/
def toCorridor
    {Γ Γc : TypeEnv} {σ σreentry : State} {cond : CppCond} {body : CppStmt}
    {Reentry : Prop}
    (h : LoopBackedgeConstructionWitness Γ Γc σ σreentry cond body Reentry) :
    Instantiate.Easy.LoopBackedgeCorridor Γ Γc σ σreentry cond body Reentry where
  stability := h.stability
  reentryEq := h.reentryEq
  reentryBoundary := h.reentryBoundary
  certificate := h.certificate

end LoopBackedgeConstructionWitness

/-- Lower-layer construction theorem for while backedges.

This is the concrete source of the Easy loop-backedge corridor.  It is still not
the whole loop classification theorem; it only constructs the local normal/continue
handoff back to the next guard. -/
structure LoopBackedgeConstructionTheorem : Type where
  bodyNormal :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .normal σb →
        Σ Reentry : Prop,
          LoopBackedgeConstructionWitness Γ Γc σ σb cond body Reentry
  bodyContinue :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .continueResult σb →
        Σ Reentry : Prop,
          LoopBackedgeConstructionWitness Γ Γc σ σb cond body Reentry

/-- Convert lower-layer backedge construction into the Easy backedge corridor theorem. -/
def loopBackedgeCorridorTheorem_of_construction
    (C : LoopBackedgeConstructionTheorem) :
    Instantiate.Easy.LoopBackedgeCorridorTheorem where
  bodyNormal := by
    intro Γ Γc σ σc σb cond body boundary condition condTrue bodyBoundary bodyNormal
    rcases C.bodyNormal boundary condition condTrue bodyBoundary bodyNormal with
      ⟨Reentry, witness⟩
    exact ⟨Reentry, witness.toCorridor⟩
  bodyContinue := by
    intro Γ Γc σ σc σb cond body boundary condition condTrue bodyBoundary bodyContinue
    rcases C.bodyContinue boundary condition condTrue bodyBoundary bodyContinue with
      ⟨Reentry, witness⟩
    exact ⟨Reentry, witness.toCorridor⟩

/-- Concrete lower-layer theorem bundle for all local-control corridors.

This is the first requested concretization target for `StepLoopFinal`:
`localCorridors` is no longer supplied directly as an Easy interface; it is
constructed from stability / boundary / reentry construction facts. -/
structure LocalControlConstructionTheorems : Type where
  seq : SeqTailStabilityConstructionTheorem
  blockTail : BlockTailStabilityConstructionTheorem
  branch : SelectedBranchStabilityConstructionTheorem
  whileBody : LoopBodyEntryBoundaryConstructionTheorem
  whileBackedge : LoopBackedgeConstructionTheorem

/-- Build the Easy local-control corridor bundle from concrete lower-layer facts. -/
def localControlCorridorTheorems_of_construction
    (C : LocalControlConstructionTheorems) :
    Instantiate.Easy.LocalControlCorridorTheorems where
  seq := seqExecutionCorridorTheorem_of_stability C.seq
  blockTail := blockTailExecutionCorridorTheorem_of_stability C.blockTail
  branch := selectedBranchCorridorTheorem_of_stability C.branch
  whileBody := loopBodyEntryCorridorTheorem_of_boundary C.whileBody
  whileBackedge := loopBackedgeCorridorTheorem_of_construction C.whileBackedge

end LocalCorridors
end Derive
end Soundness
end Cpp3
