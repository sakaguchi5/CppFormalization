import CppFormalization.Cpp3.Soundness2.Source.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

Source vocabulary for while-loop behavior.

This file keeps the behavior explanation separate from boundary entry.  Unlike the
first Soundness2 skeleton, classification is no longer a raw field of the loop
certificate: finite/divergent behavior sources are translated to
`Semantics.StmtClassified` here.
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

namespace FiniteLoopTrace

/-- A finite loop trace is exactly a finite big-step execution of the while
statement. -/
def bigStep
    {cond : CppCond} {body : CppStmt} {σ σout : State} {r : CtrlResult}
    (trace : FiniteLoopTrace cond body σ r σout) :
    Semantics.BigStepStmt σ (.whileStmt cond body) r σout := by
  induction trace with
  | falseExit condFalse =>
      exact Semantics.BigStepStmt.whileFalse condFalse
  | breakExit condTrue bodyBreak =>
      exact Semantics.BigStepStmt.whileBodyBreak condTrue bodyBreak
  | returnExit condTrue bodyReturn =>
      exact Semantics.BigStepStmt.whileBodyReturn condTrue bodyReturn
  | reenter step tail ih =>
      cases step with
      | bodyNormal condTrue bodyStep =>
          exact Semantics.BigStepStmt.whileBodyNormal condTrue bodyStep ih
      | bodyContinue condTrue bodyStep =>
          exact Semantics.BigStepStmt.whileBodyContinue condTrue bodyStep ih

/-- A finite loop trace classifies the while statement by termination. -/
def classification
    {cond : CppCond} {body : CppStmt} {σ σout : State} {r : CtrlResult}
    (trace : FiniteLoopTrace cond body σ r σout) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  Or.inl ⟨r, σout, trace.bigStep⟩

end FiniteLoopTrace

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

namespace DivergentLoopTrace

/-- A divergent loop trace is exactly a statement-divergence proof for the while
statement. -/
def stmtDiv
    {σ : State} {cond : CppCond} {body : CppStmt}
    (trace : DivergentLoopTrace σ cond body) :
    Semantics.StmtDiv σ (.whileStmt cond body) := by
  cases trace with
  | bodyDiverges condTrue bodyDiv =>
      exact Semantics.StmtDiv.whileBody condTrue bodyDiv
  | forever prefixes =>
      exact Semantics.StmtDiv.whileForever prefixes

/-- A divergent loop trace classifies the while statement by divergence. -/
def classification
    {σ : State} {cond : CppCond} {body : CppStmt}
    (trace : DivergentLoopTrace σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  Or.inr trace.stmtDiv

end DivergentLoopTrace

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

/-- A behavior source classifies the while statement as finite or divergent. -/
def classification
    {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorSource σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  match h with
  | .finite trace => trace.classification
  | .divergent trace => trace.classification

end LoopBehaviorSource

/-- Loop behavior certificate with visible safety surfaces.

Classification is no longer a raw field: it is derived from `behavior`. -/
structure LoopBehaviorCertificate
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  behavior : LoopBehaviorSource σ cond body

namespace LoopBehaviorCertificate

/-- Project the closed statement soundness target for the while statement. -/
def closedWhileSoundness
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorCertificate Γ Γc σ cond body) :
    Semantics.StmtClassified σ (.whileStmt cond body) :=
  h.behavior.classification

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
