import CppFormalization.Cpp4.Semantics.Divergence.Atom
import CppFormalization.Cpp4.Semantics.Kernel.Plan

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Plan

Divergence vocabulary for ControlPlan execution.

The rules mirror the finite kernel's control decomposition and keep `ControlPlan`
as the primary semantic target.
-/

namespace Cpp4

mutual

/-- A ControlPlan diverges. -/
inductive DivergesPlan (χ : KernelContext) : State → ControlPlan → Prop where
  | atom {σ : State} {a : ControlAtom} :
      DivergesAtom χ σ a →
      DivergesPlan χ σ (.atom a)
  | seqHead {σ : State} {head tail : ControlPlan} :
      DivergesPlan χ σ head →
      DivergesPlan χ σ (.seq head tail)
  | seqTail {σ σ₁ : State} {head tail : ControlPlan} :
      BigStepPlan χ σ head .normal σ₁ →
      DivergesPlan χ σ₁ tail →
      DivergesPlan χ σ (.seq head tail)
  | branchCond {σ : State} {c : CppCond} {thenPlan elsePlan : ControlPlan} :
      DivergesValue.Cond χ σ c →
      DivergesPlan χ σ (.branch c thenPlan elsePlan)
  | branchTrue {σ σc : State} {c : CppCond} {thenPlan elsePlan : ControlPlan} :
      BigStepValue.CondValue χ σ c true σc →
      DivergesPlan χ σc thenPlan →
      DivergesPlan χ σ (.branch c thenPlan elsePlan)
  | branchFalse {σ σc : State} {c : CppCond} {thenPlan elsePlan : ControlPlan} :
      BigStepValue.CondValue χ σ c false σc →
      DivergesPlan χ σc elsePlan →
      DivergesPlan χ σ (.branch c thenPlan elsePlan)
  | scopeFrame {σ : State} {body : PlanBlock} :
      DivergesBlock χ (KernelState.openScope σ) body →
      DivergesPlan χ σ (.scopeFrame body)
  | loopFrame {σ : State} {l : LoopPlan} :
      DivergesLoop χ σ l →
      DivergesPlan χ σ (.loopFrame l)
  | switchFrameCond {σ : State} {cond : CppSwitchCond} {arms : SwitchPlanArmList} :
      DivergesValue.SwitchCond χ σ cond →
      DivergesPlan χ σ (.switchFrame cond arms)
  | switchFrameSuffix {σ σc : State} {cond : CppSwitchCond}
      {arms suffix : SwitchPlanArmList} {n : Int} :
      BigStepValue.SwitchCondValue χ σ cond n σc →
      SwitchSuffixSelected n arms suffix →
      DivergesSwitchSuffix χ σc suffix →
      DivergesPlan χ σ (.switchFrame cond arms)
  | switchSuffix {σ : State} {arms : SwitchPlanArmList} :
      DivergesSwitchSuffix χ σ arms →
      DivergesPlan χ σ (.switchSuffix arms)

/-- A PlanBlock diverges. -/
inductive DivergesBlock (χ : KernelContext) : State → PlanBlock → Prop where
  | consHead {σ : State} {head : ControlPlan} {tail : PlanBlock} :
      DivergesPlan χ σ head →
      DivergesBlock χ σ (.cons head tail)
  | consTail {σ σ₁ : State} {head : ControlPlan} {tail : PlanBlock} :
      BigStepPlan χ σ head .normal σ₁ →
      DivergesBlock χ σ₁ tail →
      DivergesBlock χ σ (.cons head tail)

/-- A LoopPlan diverges. -/
inductive DivergesLoop (χ : KernelContext) : State → LoopPlan → Prop where
  | preTestCond {σ : State} {c : CppCond} {body : ControlPlan} :
      DivergesValue.Cond χ σ c →
      DivergesLoop χ σ (.preTest c body)
  | preTestBody {σ σc : State} {c : CppCond} {body : ControlPlan} :
      BigStepValue.CondValue χ σ c true σc →
      DivergesPlan χ σc body →
      DivergesLoop χ σ (.preTest c body)
  | preTestReentryNormal {σ σc σbody : State} {c : CppCond} {body : ControlPlan} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc body .normal σbody →
      DivergesLoop χ σbody (.preTest c body) →
      DivergesLoop χ σ (.preTest c body)
  | preTestReentryContinue {σ σc σbody : State} {c : CppCond} {body : ControlPlan} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc body .continueResult σbody →
      DivergesLoop χ σbody (.preTest c body) →
      DivergesLoop χ σ (.preTest c body)
  | postTestBody {σ : State} {body : ControlPlan} {c : CppCond} :
      DivergesPlan χ σ body →
      DivergesLoop χ σ (.postTest body c)
  | postTestCondNormal {σ σbody : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .normal σbody →
      DivergesValue.Cond χ σbody c →
      DivergesLoop χ σ (.postTest body c)
  | postTestCondContinue {σ σbody : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .continueResult σbody →
      DivergesValue.Cond χ σbody c →
      DivergesLoop χ σ (.postTest body c)
  | postTestReentryNormal {σ σbody σc : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .normal σbody →
      BigStepValue.CondValue χ σbody c true σc →
      DivergesLoop χ σc (.postTest body c) →
      DivergesLoop χ σ (.postTest body c)
  | postTestReentryContinue {σ σbody σc : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .continueResult σbody →
      BigStepValue.CondValue χ σbody c true σc →
      DivergesLoop χ σc (.postTest body c) →
      DivergesLoop χ σ (.postTest body c)
  | forInit {σ : State} {init : CppForInit} {cond : Option CppCond}
      {iter : CppForIter} {body : ControlPlan} :
      DivergesForInit χ σ init →
      DivergesLoop χ σ (.forFrame init cond iter body)
  | forRemainder {σ σinit : State} {init : CppForInit} {cond : Option CppCond}
      {iter : CppForIter} {body : ControlPlan} :
      BigStepForInit χ σ init σinit →
      DivergesForRemainder χ σinit cond iter body →
      DivergesLoop χ σ (.forFrame init cond iter body)

/-- The remainder of a for-loop diverges after initialization. -/
inductive DivergesForRemainder (χ : KernelContext) :
    State → Option CppCond → CppForIter → ControlPlan → Prop where
  | cond {σ : State} {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} :
      (match cond with | none => False | some c => DivergesValue.Cond χ σ c) →
      DivergesForRemainder χ σ cond iter body
  | body {σ σc : State} {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondTrue χ σ cond σc →
      DivergesPlan χ σc body →
      DivergesForRemainder χ σ cond iter body
  | iterNormal {σ σc σbody : State} {cond : Option CppCond}
      {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .normal σbody →
      DivergesForIter χ σbody iter →
      DivergesForRemainder χ σ cond iter body
  | iterContinue {σ σc σbody : State} {cond : Option CppCond}
      {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .continueResult σbody →
      DivergesForIter χ σbody iter →
      DivergesForRemainder χ σ cond iter body
  | reentryNormal {σ σc σbody σiter : State} {cond : Option CppCond}
      {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .normal σbody →
      BigStepForIter χ σbody iter σiter →
      DivergesForRemainder χ σiter cond iter body →
      DivergesForRemainder χ σ cond iter body
  | reentryContinue {σ σc σbody σiter : State} {cond : Option CppCond}
      {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .continueResult σbody →
      BigStepForIter χ σbody iter σiter →
      DivergesForRemainder χ σiter cond iter body →
      DivergesForRemainder χ σ cond iter body

/-- An already-selected switch suffix diverges. -/
inductive DivergesSwitchSuffix (χ : KernelContext) : State → SwitchPlanArmList → Prop where
  | armBody {σ : State} {label : SwitchLabel} {body : PlanBlock}
      {rest : SwitchPlanArmList} :
      DivergesBlock χ σ body →
      DivergesSwitchSuffix χ σ (.cons (.arm label body) rest)
  | fallthrough {σ σbody : State} {label : SwitchLabel} {body : PlanBlock}
      {rest : SwitchPlanArmList} :
      BigStepBlock χ σ body .normal σbody →
      DivergesSwitchSuffix χ σbody rest →
      DivergesSwitchSuffix χ σ (.cons (.arm label body) rest)

end

end Cpp4
