import CppFormalization.Cpp3.Soundness2.Source.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

Source vocabulary for while-loop behavior.

This file keeps the behavior explanation separate from the final classification
fact.  The classification fact is explicit, avoiding any hidden termination or
divergence oracle in the boundary layer.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- One reentry step of a while loop, through body normal or continue. -/
inductive LoopReentryStep (σ : State) (cond : CppCond) (body : CppStmt) : State → Type where
  | bodyNormal
      {σc σb : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyStep : Semantics.BigStepStmt σc body .normal σb) :
      LoopReentryStep σ cond body σb
  | bodyContinue
      {σc σb : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyStep : Semantics.BigStepStmt σc body .continueResult σb) :
      LoopReentryStep σ cond body σb

/-- Finite loop trace explanation.  This is an explanatory source, not a hidden
proof that all loops terminate. -/
inductive FiniteLoopTrace (cond : CppCond) (body : CppStmt) :
    State → CtrlResult → State → Type where
  | falseExit
      {σ σc : State}
      (condFalse : Semantics.BigStepCond σ cond false σc) :
      FiniteLoopTrace cond body σ .normal σc

  | breakExit
      {σ σc σb : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyBreak : Semantics.BigStepStmt σc body .breakResult σb) :
      FiniteLoopTrace cond body σ .normal σb

  | returnExit
      {σ σc σb : State} {ov : Option Value}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyReturn : Semantics.BigStepStmt σc body (.returnResult ov) σb) :
      FiniteLoopTrace cond body σ (.returnResult ov) σb

  | reenter
      {σ σb σout : State} {r : CtrlResult}
      (step : LoopReentryStep σ cond body σb)
      (tail : FiniteLoopTrace cond body σb r σout) :
      FiniteLoopTrace cond body σ r σout


/-- Divergent loop explanation. -/
inductive DivergentLoopTrace (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | bodyDiverges
      {σc : State}
      (condTrue : Semantics.BigStepCond σ cond true σc)
      (bodyDiv : Semantics.StmtDiv σc body) :
      DivergentLoopTrace σ cond body
  | forever
      (prefixes : ∀ n : Nat, ∃ σn : State,
        Semantics.WhilePrefix n σ cond body σn) :
      DivergentLoopTrace σ cond body

/-- Behavior explanation for one concrete while entry. -/
inductive LoopBehaviorSource
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | finite
      {σout : State} {r : CtrlResult}
      (trace : FiniteLoopTrace cond body σ r σout) :
      LoopBehaviorSource σ cond body
  | divergent
      (trace : DivergentLoopTrace σ cond body) :
      LoopBehaviorSource σ cond body

namespace LoopBehaviorSource

/-- Build a behavior source for body divergence. -/
def bodyDiverges
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyDiv : Semantics.StmtDiv σc body) :
    LoopBehaviorSource σ cond body :=
  .divergent (.bodyDiverges condTrue bodyDiv)

/-- Build a behavior source for productive forever reentry. -/
def forever
    {σ : State} {cond : CppCond} {body : CppStmt}
    (prefixes : ∀ n : Nat, ∃ σn : State,
      Semantics.WhilePrefix n σ cond body σn) :
    LoopBehaviorSource σ cond body :=
  .divergent (.forever prefixes)

end LoopBehaviorSource

/-- Loop behavior certificate with visible safety surfaces and explicit semantic
classification. -/
structure LoopBehaviorCertificate
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  behavior : LoopBehaviorSource σ cond body
  classification : Semantics.StmtClassified σ (.whileStmt cond body)

namespace LoopBehaviorCertificate

/-- Project the closed statement soundness target for the while statement. -/
def closedWhileSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorCertificate Γ Γc σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  h.classification

end LoopBehaviorCertificate

/-- Source theorem for producing loop behavior certificates from while boundaries. -/
structure LoopBehaviorCertificateTheorem : Type where
  certify :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopBehaviorCertificate Γ Γc σ cond body

end Source
end Soundness2
end Cpp3
