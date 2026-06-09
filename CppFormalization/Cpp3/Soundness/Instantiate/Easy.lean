import CppFormalization.Cpp3.Soundness.Instantiate.While

/-!
# CppFormalization.Cpp3.Soundness.Instantiate.Easy

Local-control corridor instantiation for the easy soundness providers.

This file separates the genuinely semantic residual providers
(`BlockCloseProvider` and `WhileReentrySoundnessProvider`) from the local
control-transfer providers.  The easy providers are now obtained by small
conversion theorems from C++-facing corridor/stability packages:

* sequence head normal route to statement tail;
* block head normal route to block tail;
* selected if-branch route;
* while true-guard entry into the body;
* while normal/continue backedge to the next guard.

The point is not to hide assumptions under new names.  Each corridor is a
Boundary/Stability/Continuation/SafetyFragment-facing object that later files can
construct from the concrete lower-layer preservation facts.
-/

namespace Cpp3
namespace Soundness
namespace Instantiate
namespace Easy

/-- C++ corridor from a normally completed sequence head to its statement tail. -/
structure SeqExecutionCorridor
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  stability : Stability.SeqTailStability Γ Θ σ σ₁ head tail

namespace SeqExecutionCorridor

/-- Consume a sequence corridor as the continuation surface required by Soundness. -/
def toContinuation
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqExecutionCorridor Γ Θ σ σ₁ head tail) :
    Continuation.SeqTailContinuation Γ Θ σ σ₁ head tail where
  stability := h.stability

end SeqExecutionCorridor

/-- Lower-layer theorem surface for constructing sequence execution corridors. -/
structure SeqExecutionCorridorTheorem : Type where
  corridor :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt},
      Boundary.StmtBoundary Γ σ (.seq head tail) →
      Semantics.SeqNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          SeqExecutionCorridor Γ Θ σ σ₁ head tail

/-- The old sequence continuation provider is just corridor-to-continuation glue. -/
def seqContinuationProvider_of_corridor
    (C : SeqExecutionCorridorTheorem) :
    SeqContinuationProvider where
  provide := by
    intro Γ σ σ₁ head tail boundary route
    rcases C.corridor boundary route with ⟨Θ, corridor⟩
    exact ⟨Θ, corridor.toContinuation⟩

/-- C++ corridor from a normally completed block head to the block tail. -/
structure BlockTailExecutionCorridor
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  stability : Stability.BlockTailStability Γ Θ σ σ₁ head tail

namespace BlockTailExecutionCorridor

/-- Consume a block-tail corridor as the continuation surface required by Soundness. -/
def toContinuation
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailExecutionCorridor Γ Θ σ σ₁ head tail) :
    Continuation.BlockTailContinuation Γ Θ σ σ₁ head tail where
  stability := h.stability

end BlockTailExecutionCorridor

/-- Lower-layer theorem surface for constructing block-tail execution corridors. -/
structure BlockTailExecutionCorridorTheorem : Type where
  corridor :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock},
      Boundary.BlockBoundary Γ σ (.cons head tail) →
      Semantics.BlockConsNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          BlockTailExecutionCorridor Γ Θ σ σ₁ head tail

/-- The old block-tail continuation provider is just corridor-to-continuation glue. -/
def blockTailContinuationProvider_of_corridor
    (C : BlockTailExecutionCorridorTheorem) :
    BlockTailContinuationProvider where
  provide := by
    intro Γ σ σ₁ head tail boundary route
    rcases C.corridor boundary route with ⟨Θ, corridor⟩
    exact ⟨Θ, corridor.toContinuation⟩

/-- C++ corridor from a condition route to the selected branch. -/
structure SelectedBranchCorridor
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) (side : Semantics.BranchSide) : Type where
  stability : Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side

namespace SelectedBranchCorridor

/-- Consume a selected-branch corridor as the continuation surface required by Soundness. -/
def toContinuation
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchCorridor Γ Γc σ σc cond thenBranch elseBranch side) :
    Continuation.SelectedBranchContinuation Γ Γc σ σc cond thenBranch elseBranch side where
  stability := h.stability

end SelectedBranchCorridor

/-- Lower-layer theorem surface for constructing the selected branch corridor. -/
structure SelectedBranchCorridorTheorem : Type where
  select :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
        (Σ Γc : TypeEnv,
          Σ σc : State,
            SelectedBranchCorridor Γ Γc σ σc cond thenBranch elseBranch
              Semantics.BranchSide.thenBranch) ⊕
        (Σ Γc : TypeEnv,
          Σ σc : State,
            SelectedBranchCorridor Γ Γc σ σc cond thenBranch elseBranch
              Semantics.BranchSide.elseBranch)

/-- The old branch continuation provider is just corridor-to-continuation glue. -/
def branchContinuationProvider_of_corridor
    (C : SelectedBranchCorridorTheorem) :
    BranchContinuationProvider where
  select := by
    intro Γ σ cond thenBranch elseBranch boundary
    cases C.select boundary with
    | inl selected =>
        rcases selected with ⟨Γc, σc, corridor⟩
        exact Sum.inl ⟨Γc, σc, corridor.toContinuation⟩
    | inr selected =>
        rcases selected with ⟨Γc, σc, corridor⟩
        exact Sum.inr ⟨Γc, σc, corridor.toContinuation⟩

/-- C++ corridor from a true while guard to the loop body entry. -/
structure LoopBodyEntryCorridor
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond) (body : CppStmt) : Type where
  source : Boundary.StmtBoundary Γ σ (.whileStmt cond body)
  condition : Boundary.CondBoundary Γ Γc σ cond
  condTrue : Semantics.BigStepCond σ cond true σc
  bodyBoundary : Boundary.StmtBoundary Γc σc body

/-- Lower-layer theorem surface for constructing while-body entry corridors. -/
structure LoopBodyEntryCorridorTheorem : Type where
  corridor :
    ∀ {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
        LoopBodyEntryCorridor Γ Γc σ σc cond body

/-- The old while-body boundary provider is just corridor projection. -/
def whileBodyBoundaryProvider_of_corridor
    (C : LoopBodyEntryCorridorTheorem) :
    WhileBodyBoundaryProvider where
  provide := by
    intro Γ Γc σ σc cond body boundary condition condStep
    exact (C.corridor boundary condition condStep).bodyBoundary

/-- C++ corridor from a normal/continue loop body result back to the next guard. -/
structure LoopBackedgeCorridor
    (Γ Γc : TypeEnv) (σ σreentry : State) (cond : CppCond) (body : CppStmt)
    (Reentry : Prop) : Type where
  stability : Stability.WhileBoundaryStability Γ Γc σ cond body
  reentryEq : Stability.WhileBoundaryStability.routePostState stability = σreentry
  reentryBoundary : Boundary.StmtBoundary Γ σreentry (.whileStmt cond body)
  certificate : Continuation.ContinuationCertificate Reentry

namespace LoopBackedgeCorridor

/-- Consume a loop-backedge corridor as the continuation surface required by Soundness. -/
def toContinuation
    {Γ Γc : TypeEnv} {σ σreentry : State} {cond : CppCond} {body : CppStmt}
    {Reentry : Prop}
    (h : LoopBackedgeCorridor Γ Γc σ σreentry cond body Reentry) :
    Continuation.WhileReentryContinuation Γ Γc σ σreentry cond body Reentry :=
  let boundary : Continuation.WhileBoundaryContinuation Γ Γc σ cond body := {
    stability := h.stability
  }
  {
    boundary := boundary
    reentryEq := by
      show boundary.routePostState = σreentry
      exact h.reentryEq
    reentryBoundary := h.reentryBoundary
    certificate := h.certificate
  }

end LoopBackedgeCorridor

/-- Lower-layer theorem surface for constructing while backedge corridors. -/
structure LoopBackedgeCorridorTheorem : Type where
  bodyNormal :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .normal σb →
        Σ Reentry : Prop,
          LoopBackedgeCorridor Γ Γc σ σb cond body Reentry
  bodyContinue :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .continueResult σb →
        Σ Reentry : Prop,
          LoopBackedgeCorridor Γ Γc σ σb cond body Reentry

/-- The old while-reentry continuation provider is just corridor-to-continuation glue. -/
def whileReentryContinuationProvider_of_corridor
    (C : LoopBackedgeCorridorTheorem) :
    WhileReentryContinuationProvider where
  bodyNormalReentry := by
    intro Γ Γc σ σc σb cond body boundary condition condStep bodyBoundary bodyNormal
    -- C.bodyNormal が返す corridor を .toContinuation で変換する
    match C.bodyNormal boundary condition condStep bodyBoundary bodyNormal with
    | ⟨Reentry, corridor⟩ =>
        exact ⟨Reentry, corridor.toContinuation⟩
  bodyContinueReentry := by
    intro Γ Γc σ σc σb cond body boundary condition condStep bodyBoundary bodyContinue
    -- 同様に C.bodyContinue が返す corridor を変換する
    match C.bodyContinue boundary condition condStep bodyBoundary bodyContinue with
    | ⟨Reentry, corridor⟩ =>
        exact ⟨Reentry, corridor.toContinuation⟩

/-- Easy local-control corridor theorem bundle.

This is the replacement for five provider-shaped Soundness assumptions.  The two
remaining hard providers are intentionally excluded: block scope close and while
reentry classification. -/
structure LocalControlCorridorTheorems : Type where
  seq : SeqExecutionCorridorTheorem
  blockTail : BlockTailExecutionCorridorTheorem
  branch : SelectedBranchCorridorTheorem
  whileBody : LoopBodyEntryCorridorTheorem
  whileBackedge : LoopBackedgeCorridorTheorem

/-- Build the first-five providers from easy corridors plus the residual block-close provider. -/
def firstFiveProviders_of_easy
    (C : LocalControlCorridorTheorems)
    (blockClose : BlockCloseProvider) :
    FirstFiveProviders where
  seq := seqContinuationProvider_of_corridor C.seq
  blockTail := blockTailContinuationProvider_of_corridor C.blockTail
  branch := branchContinuationProvider_of_corridor C.branch
  blockClose := blockClose

/-- Build the while-clause providers from easy loop-entry/backedge corridors. -/
def whileClauseProviders_of_easy
    (C : LocalControlCorridorTheorems) :
    WhileClauseProviders where
  body := whileBodyBoundaryProvider_of_corridor C.whileBody
  reentry := whileReentryContinuationProvider_of_corridor C.whileBackedge

end Easy
end Instantiate
end Soundness
end Cpp3
