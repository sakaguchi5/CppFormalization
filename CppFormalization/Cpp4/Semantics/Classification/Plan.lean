import CppFormalization.Cpp4.Semantics.Divergence.Plan

/-!
# CppFormalization.Cpp4.Semantics.Classification.Plan

Execution classification for ControlPlan finite/divergent outcomes.
-/

namespace Cpp4

/-- Classification of a ControlPlan execution attempt. -/
inductive PlanClassification (χ : KernelContext) (σ : State) (p : ControlPlan) : Type where
  | finite {r : CtrlResult} {σ' : State} (step : BigStepPlan χ σ p r σ') :
      PlanClassification χ σ p
  | diverges (diverges : DivergesPlan χ σ p) :
      PlanClassification χ σ p

/-- Classification of a PlanBlock execution attempt. -/
inductive BlockClassification (χ : KernelContext) (σ : State) (b : PlanBlock) : Type where
  | finite {r : CtrlResult} {σ' : State} (step : BigStepBlock χ σ b r σ') :
      BlockClassification χ σ b
  | diverges (diverges : DivergesBlock χ σ b) :
      BlockClassification χ σ b

/-- Classification of a LoopPlan execution attempt. -/
inductive LoopClassification (χ : KernelContext) (σ : State) (l : LoopPlan) : Type where
  | finite {r : CtrlResult} {σ' : State} (step : BigStepLoop χ σ l r σ') :
      LoopClassification χ σ l
  | diverges (diverges : DivergesLoop χ σ l) :
      LoopClassification χ σ l

/-- Classification of a selected switch suffix. -/
inductive SwitchSuffixClassification
    (χ : KernelContext) (σ : State) (arms : SwitchPlanArmList) : Type where
  | finite {r : CtrlResult} {σ' : State} (step : BigStepSwitchSuffix χ σ arms r σ') :
      SwitchSuffixClassification χ σ arms
  | diverges (diverges : DivergesSwitchSuffix χ σ arms) :
      SwitchSuffixClassification χ σ arms

namespace PlanClassification

/-- Proposition saying that a plan execution is classified as finite or divergent. -/
def SoundnessShape (χ : KernelContext) (σ : State) (p : ControlPlan) : Prop :=
  (∃ r σ', BigStepPlan χ σ p r σ') ∨ DivergesPlan χ σ p

/-- A classification provides evidence for its finite-or-divergent soundness shape. -/
def soundnessShapeEvidence {χ : KernelContext} {σ : State} {p : ControlPlan}
    (h : PlanClassification χ σ p) : SoundnessShape χ σ p :=
  match h with
  | .finite step => Or.inl ⟨_, _, step⟩
  | .diverges div => Or.inr div

/-- A finite step gives a classification. -/
def ofFinite {χ : KernelContext} {σ σ' : State} {p : ControlPlan} {r : CtrlResult}
    (h : BigStepPlan χ σ p r σ') : PlanClassification χ σ p :=
  .finite h

/-- A divergence proof gives a classification. -/
def ofDivergence {χ : KernelContext} {σ : State} {p : ControlPlan}
    (h : DivergesPlan χ σ p) : PlanClassification χ σ p :=
  .diverges h

end PlanClassification

end Cpp4
