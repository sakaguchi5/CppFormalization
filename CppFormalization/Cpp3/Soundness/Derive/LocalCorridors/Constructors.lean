import CppFormalization.Cpp3.Soundness.Derive.LocalCorridors

/-!
# CppFormalization.Cpp3.Soundness.Derive.LocalCorridors.Constructors

Bottom-up constructors for local-control construction facts.

`Derive.LocalCorridors` already names the construction theorem surfaces consumed by
`DerivedLoopFinal`: sequence-tail stability, block-tail stability, selected-branch
stability, while-body entry, and while backedge construction.

This file fixes the construction direction for those local-control facts.  It does
not introduce a new provider-shaped assumption.  Instead it packages the smallest
C++ local-control evidence and provides adapters from those evidence packages to
the existing construction theorem bundle.

C++ reading:

* a normally completed sequence head exposes the statement tail;
* a normally completed block head exposes the remaining block body;
* an `if` condition selects exactly one executable branch;
* a true while guard exposes the loop body;
* a normal/continue body result exposes the next guard reentry.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace LocalCorridors

/-- Bottom-up source for a sequence-tail local-control handoff. -/
structure SeqTailControlSource
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  stability : Stability.SeqTailStability Γ Θ σ σ₁ head tail

namespace SeqTailControlSource

/-- Project the concrete sequence-tail stability fact. -/
def toStability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailControlSource Γ Θ σ σ₁ head tail) :
    Stability.SeqTailStability Γ Θ σ σ₁ head tail :=
  h.stability

end SeqTailControlSource

/-- Bottom-up theorem surface for producing sequence-tail control sources. -/
structure SeqTailControlSourceTheorem : Type where
  source :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt},
      Boundary.StmtBoundary Γ σ (.seq head tail) →
      Semantics.SeqNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          SeqTailControlSource Γ Θ σ σ₁ head tail

/-- Convert bottom-up sequence-tail sources to the existing construction theorem. -/
def seqTailStabilityConstructionTheorem_of_source
    (C : SeqTailControlSourceTheorem) :
    SeqTailStabilityConstructionTheorem where
  stability := by
    intro Γ σ σ₁ head tail boundary route
    rcases C.source boundary route with ⟨Θ, source⟩
    exact ⟨Θ, source.toStability⟩

/-- Bottom-up source for a block-tail local-control handoff. -/
structure BlockTailControlSource
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  stability : Stability.BlockTailStability Γ Θ σ σ₁ head tail

namespace BlockTailControlSource

/-- Project the concrete block-tail stability fact. -/
def toStability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailControlSource Γ Θ σ σ₁ head tail) :
    Stability.BlockTailStability Γ Θ σ σ₁ head tail :=
  h.stability

end BlockTailControlSource

/-- Bottom-up theorem surface for producing block-tail control sources. -/
structure BlockTailControlSourceTheorem : Type where
  source :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock},
      Boundary.BlockBoundary Γ σ (.cons head tail) →
      Semantics.BlockConsNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          BlockTailControlSource Γ Θ σ σ₁ head tail

/-- Convert bottom-up block-tail sources to the existing construction theorem. -/
def blockTailStabilityConstructionTheorem_of_source
    (C : BlockTailControlSourceTheorem) :
    BlockTailStabilityConstructionTheorem where
  stability := by
    intro Γ σ σ₁ head tail boundary route
    rcases C.source boundary route with ⟨Θ, source⟩
    exact ⟨Θ, source.toStability⟩

/-- Bottom-up source for a selected branch local-control handoff. -/
structure SelectedBranchControlSource
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) (side : Semantics.BranchSide) : Type where
  stability : Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side

namespace SelectedBranchControlSource

/-- Project the selected-branch stability fact. -/
def toStability
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchControlSource Γ Γc σ σc cond thenBranch elseBranch side) :
    Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side :=
  h.stability

end SelectedBranchControlSource

/-- The selected branch source, keeping the actual selected side explicit. -/
inductive SelectedBranchControlSelection
    (Γ : TypeEnv) (σ : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type where
  | thenSelected
      {Γc : TypeEnv} {σc : State}
      (source : SelectedBranchControlSource Γ Γc σ σc cond thenBranch elseBranch
        Semantics.BranchSide.thenBranch) :
      SelectedBranchControlSelection Γ σ cond thenBranch elseBranch
  | elseSelected
      {Γc : TypeEnv} {σc : State}
      (source : SelectedBranchControlSource Γ Γc σ σc cond thenBranch elseBranch
        Semantics.BranchSide.elseBranch) :
      SelectedBranchControlSelection Γ σ cond thenBranch elseBranch

/-- Bottom-up theorem surface for producing selected-branch control sources. -/
structure SelectedBranchControlSourceTheorem : Type where
  select :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
        SelectedBranchControlSelection Γ σ cond thenBranch elseBranch

/-- Convert bottom-up selected-branch sources to the existing construction theorem. -/
def selectedBranchStabilityConstructionTheorem_of_source
    (C : SelectedBranchControlSourceTheorem) :
    SelectedBranchStabilityConstructionTheorem where
  select := by
    intro Γ σ cond thenBranch elseBranch boundary
    match C.select boundary with
    | .thenSelected source =>
        exact Sum.inl ⟨_, _, source.toStability⟩
    | .elseSelected source =>
        exact Sum.inr ⟨_, _, source.toStability⟩

/-- Bottom-up source for entering a while body after a true guard. -/
structure LoopBodyEntryControlSource
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond) (body : CppStmt) : Type where
  source : Boundary.StmtBoundary Γ σ (.whileStmt cond body)
  condition : Boundary.CondBoundary Γ Γc σ cond
  condTrue : Semantics.BigStepCond σ cond true σc
  bodyBoundary : Boundary.StmtBoundary Γc σc body

namespace LoopBodyEntryControlSource

/-- Project the body-entry boundary from the source. -/
def toBodyBoundary
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBodyEntryControlSource Γ Γc σ σc cond body) :
    Boundary.StmtBoundary Γc σc body :=
  h.bodyBoundary

end LoopBodyEntryControlSource

/-- Bottom-up theorem surface for producing while-body entry sources. -/
structure LoopBodyEntryControlSourceTheorem : Type where
  source :
    ∀ {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
        LoopBodyEntryControlSource Γ Γc σ σc cond body

/-- Convert bottom-up while-body sources to the existing construction theorem. -/
def loopBodyEntryBoundaryConstructionTheorem_of_source
    (C : LoopBodyEntryControlSourceTheorem) :
    LoopBodyEntryBoundaryConstructionTheorem where
  bodyBoundary := by
    intro Γ Γc σ σc cond body boundary condition condTrue
    exact (C.source boundary condition condTrue).toBodyBoundary

/-- Bottom-up source for a while normal/continue backedge. -/
structure LoopBackedgeControlSource
    (Γ Γc : TypeEnv) (σ σreentry : State) (cond : CppCond) (body : CppStmt)
    (Reentry : Prop) : Type where
  stability : Stability.WhileBoundaryStability Γ Γc σ cond body
  reentryEq : Stability.WhileBoundaryStability.routePostState stability = σreentry
  reentryBoundary : Boundary.StmtBoundary Γ σreentry (.whileStmt cond body)
  certificate : Continuation.ContinuationCertificate Reentry

namespace LoopBackedgeControlSource

/-- Convert the bottom-up source into the existing backedge construction witness. -/
def toWitness
    {Γ Γc : TypeEnv} {σ σreentry : State} {cond : CppCond} {body : CppStmt}
    {Reentry : Prop}
    (h : LoopBackedgeControlSource Γ Γc σ σreentry cond body Reentry) :
    LoopBackedgeConstructionWitness Γ Γc σ σreentry cond body Reentry where
  stability := h.stability
  reentryEq := h.reentryEq
  reentryBoundary := h.reentryBoundary
  certificate := h.certificate

end LoopBackedgeControlSource

/-- Bottom-up theorem surface for producing while-backedge control sources. -/
structure LoopBackedgeControlSourceTheorem : Type where
  bodyNormal :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .normal σb →
        Σ Reentry : Prop,
          LoopBackedgeControlSource Γ Γc σ σb cond body Reentry
  bodyContinue :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .continueResult σb →
        Σ Reentry : Prop,
          LoopBackedgeControlSource Γ Γc σ σb cond body Reentry

/-- Convert bottom-up while-backedge sources to the existing construction theorem. -/
def loopBackedgeConstructionTheorem_of_source
    (C : LoopBackedgeControlSourceTheorem) :
    LoopBackedgeConstructionTheorem where
  bodyNormal := by
    intro Γ Γc σ σc σb cond body boundary condition condTrue bodyBoundary bodyNormal
    rcases C.bodyNormal boundary condition condTrue bodyBoundary bodyNormal with
      ⟨Reentry, source⟩
    exact ⟨Reentry, source.toWitness⟩
  bodyContinue := by
    intro Γ Γc σ σc σb cond body boundary condition condTrue bodyBoundary bodyContinue
    rcases C.bodyContinue boundary condition condTrue bodyBoundary bodyContinue with
      ⟨Reentry, source⟩
    exact ⟨Reentry, source.toWitness⟩

/-- Bottom-up source bundle for all local-control construction facts. -/
structure LocalControlSourceTheorems : Type where
  seq : SeqTailControlSourceTheorem
  blockTail : BlockTailControlSourceTheorem
  branch : SelectedBranchControlSourceTheorem
  whileBody : LoopBodyEntryControlSourceTheorem
  whileBackedge : LoopBackedgeControlSourceTheorem

/-- Build the existing local-control construction bundle from bottom-up sources. -/
def localControlConstructionTheorems_of_sources
    (C : LocalControlSourceTheorems) :
    LocalControlConstructionTheorems where
  seq := seqTailStabilityConstructionTheorem_of_source C.seq
  blockTail := blockTailStabilityConstructionTheorem_of_source C.blockTail
  branch := selectedBranchStabilityConstructionTheorem_of_source C.branch
  whileBody := loopBodyEntryBoundaryConstructionTheorem_of_source C.whileBody
  whileBackedge := loopBackedgeConstructionTheorem_of_source C.whileBackedge

/-- Compose bottom-up local-control sources directly to the Easy corridor bundle. -/
def localControlCorridorTheorems_of_sources
    (C : LocalControlSourceTheorems) :
    Instantiate.Easy.LocalControlCorridorTheorems :=
  localControlCorridorTheorems_of_construction
    (localControlConstructionTheorems_of_sources C)

end LocalCorridors
end Derive
end Soundness
end Cpp3
