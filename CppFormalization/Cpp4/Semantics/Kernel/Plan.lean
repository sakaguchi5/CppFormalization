import CppFormalization.Cpp4.Core.ControlPlan
import CppFormalization.Cpp4.Semantics.Kernel.Atom

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Plan

Finite kernel semantics for `ControlPlan`, plan blocks, loop plans, and selected
switch suffixes.
-/

namespace Cpp4

/-- Optional `for` condition succeeds when absent or when the condition evaluates to
`true`. -/
inductive BigStepOptionalCondTrue (χ : KernelContext) :
    State → Option CppCond → State → Prop where
  | absent {σ : State} :
      BigStepOptionalCondTrue χ σ none σ
  | present {σ σ' : State} {c : CppCond} :
      BigStepValue.CondValue χ σ c true σ' →
      BigStepOptionalCondTrue χ σ (some c) σ'

/-- Optional `for` condition fails only when a present condition evaluates to
`false`. -/
inductive BigStepOptionalCondFalse (χ : KernelContext) :
    State → Option CppCond → State → Prop where
  | present {σ σ' : State} {c : CppCond} :
      BigStepValue.CondValue χ σ c false σ' →
      BigStepOptionalCondFalse χ σ (some c) σ'

/-- Integer switch label matching for the first switch kernel.  `default` is modeled
as an available fallback; later Static/Switch can refine uniqueness and selection
priority. -/
inductive SwitchLabelMatches (n : Int) : SwitchLabel → Prop where
  | caseInt : SwitchLabelMatches n (.caseInt n)
  | defaultLabel : SwitchLabelMatches n .defaultLabel

/-- Select a fallthrough suffix from a switch arm list. -/
inductive SwitchSuffixSelected (n : Int) :
    SwitchPlanArmList → SwitchPlanArmList → Prop where
  | here {label : SwitchLabel} {body : PlanBlock} {rest : SwitchPlanArmList} :
      SwitchLabelMatches n label →
      SwitchSuffixSelected n (.cons (.arm label body) rest) (.cons (.arm label body) rest)
  | tail {arm : SwitchPlanArm} {rest suffix : SwitchPlanArmList} :
      SwitchSuffixSelected n rest suffix →
      SwitchSuffixSelected n (.cons arm rest) suffix

mutual

/-- Finite execution of a ControlPlan. -/
inductive BigStepPlan (χ : KernelContext) :
    State → ControlPlan → CtrlResult → State → Prop where
  | atom {σ σ' : State} {a : ControlAtom} {r : CtrlResult} :
      BigStepAtom χ σ a r σ' →
      BigStepPlan χ σ (.atom a) r σ'
  | seqNormal {σ σ₁ σ₂ : State} {head tail : ControlPlan} {r : CtrlResult} :
      BigStepPlan χ σ head .normal σ₁ →
      BigStepPlan χ σ₁ tail r σ₂ →
      BigStepPlan χ σ (.seq head tail) r σ₂
  | seqBreak {σ σ' : State} {head tail : ControlPlan} :
      BigStepPlan χ σ head .breakResult σ' →
      BigStepPlan χ σ (.seq head tail) .breakResult σ'
  | seqCont {σ σ' : State} {head tail : ControlPlan} :
      BigStepPlan χ σ head .continueResult σ' →
      BigStepPlan χ σ (.seq head tail) .continueResult σ'
  | seqReturnVoid {σ σ' : State} {head tail : ControlPlan} :
      BigStepPlan χ σ head .returnVoid σ' →
      BigStepPlan χ σ (.seq head tail) .returnVoid σ'
  | seqReturnValue {σ σ' : State} {head tail : ControlPlan} {v : Value} :
      BigStepPlan χ σ head (.returnValue v) σ' →
      BigStepPlan χ σ (.seq head tail) (.returnValue v) σ'
  | branchTrue {σ σc σ' : State} {c : CppCond}
      {thenPlan elsePlan : ControlPlan} {r : CtrlResult} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc thenPlan r σ' →
      BigStepPlan χ σ (.branch c thenPlan elsePlan) r σ'
  | branchFalse {σ σc σ' : State} {c : CppCond}
      {thenPlan elsePlan : ControlPlan} {r : CtrlResult} :
      BigStepValue.CondValue χ σ c false σc →
      BigStepPlan χ σc elsePlan r σ' →
      BigStepPlan χ σ (.branch c thenPlan elsePlan) r σ'
  | scopeFrame {σ σbody : State} {body : PlanBlock} {r : CtrlResult} :
      BigStepBlock χ (KernelState.openScope σ) body r σbody →
      BigStepPlan χ σ (.scopeFrame body) r
        (popScopeState σbody (KernelState.nextScopeId σ))
  | loopFrame {σ σ' : State} {l : LoopPlan} {r : CtrlResult} :
      BigStepLoop χ σ l r σ' →
      BigStepPlan χ σ (.loopFrame l) r σ'
  | switchFrame {σ σc σ' : State} {cond : CppSwitchCond}
      {arms suffix : SwitchPlanArmList} {n : Int} {r : CtrlResult} :
      BigStepValue.SwitchCondValue χ σ cond n σc →
      SwitchSuffixSelected n arms suffix →
      BigStepSwitchSuffix χ σc suffix r σ' →
      BigStepPlan χ σ (.switchFrame cond arms) r σ'
  | switchSuffix {σ σ' : State} {arms : SwitchPlanArmList} {r : CtrlResult} :
      BigStepSwitchSuffix χ σ arms r σ' →
      BigStepPlan χ σ (.switchSuffix arms) r σ'

/-- Finite execution of a plan block. -/
inductive BigStepBlock (χ : KernelContext) :
    State → PlanBlock → CtrlResult → State → Prop where
  | nil {σ : State} :
      BigStepBlock χ σ .nil .normal σ
  | consNormal {σ σ₁ σ₂ : State} {head : ControlPlan} {tail : PlanBlock} {r : CtrlResult} :
      BigStepPlan χ σ head .normal σ₁ →
      BigStepBlock χ σ₁ tail r σ₂ →
      BigStepBlock χ σ (.cons head tail) r σ₂
  | consBreak {σ σ' : State} {head : ControlPlan} {tail : PlanBlock} :
      BigStepPlan χ σ head .breakResult σ' →
      BigStepBlock χ σ (.cons head tail) .breakResult σ'
  | consCont {σ σ' : State} {head : ControlPlan} {tail : PlanBlock} :
      BigStepPlan χ σ head .continueResult σ' →
      BigStepBlock χ σ (.cons head tail) .continueResult σ'
  | consReturnVoid {σ σ' : State} {head : ControlPlan} {tail : PlanBlock} :
      BigStepPlan χ σ head .returnVoid σ' →
      BigStepBlock χ σ (.cons head tail) .returnVoid σ'
  | consReturnValue {σ σ' : State} {head : ControlPlan} {tail : PlanBlock} {v : Value} :
      BigStepPlan χ σ head (.returnValue v) σ' →
      BigStepBlock χ σ (.cons head tail) (.returnValue v) σ'

/-- Finite execution of a loop plan. -/
inductive BigStepLoop (χ : KernelContext) :
    State → LoopPlan → CtrlResult → State → Prop where
  | preTestFalse {σ σc : State} {c : CppCond} {body : ControlPlan} :
      BigStepValue.CondValue χ σ c false σc →
      BigStepLoop χ σ (.preTest c body) .normal σc
  | preTestBodyNormal {σ σc σbody σ' : State} {c : CppCond} {body : ControlPlan}
      {r : CtrlResult} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc body .normal σbody →
      BigStepLoop χ σbody (.preTest c body) r σ' →
      BigStepLoop χ σ (.preTest c body) r σ'
  | preTestBodyCont {σ σc σbody σ' : State} {c : CppCond} {body : ControlPlan}
      {r : CtrlResult} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc body .continueResult σbody →
      BigStepLoop χ σbody (.preTest c body) r σ' →
      BigStepLoop χ σ (.preTest c body) r σ'
  | preTestBodyBreak {σ σc σbody : State} {c : CppCond} {body : ControlPlan} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc body .breakResult σbody →
      BigStepLoop χ σ (.preTest c body) .normal σbody
  | preTestReturnVoid {σ σc σbody : State} {c : CppCond} {body : ControlPlan} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc body .returnVoid σbody →
      BigStepLoop χ σ (.preTest c body) .returnVoid σbody
  | preTestReturnValue {σ σc σbody : State} {c : CppCond} {body : ControlPlan} {v : Value} :
      BigStepValue.CondValue χ σ c true σc →
      BigStepPlan χ σc body (.returnValue v) σbody →
      BigStepLoop χ σ (.preTest c body) (.returnValue v) σbody
  | postTestBodyBreak {σ σbody : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .breakResult σbody →
      BigStepLoop χ σ (.postTest body c) .normal σbody
  | postTestReturnVoid {σ σbody : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .returnVoid σbody →
      BigStepLoop χ σ (.postTest body c) .returnVoid σbody
  | postTestReturnValue {σ σbody : State} {body : ControlPlan} {c : CppCond} {v : Value} :
      BigStepPlan χ σ body (.returnValue v) σbody →
      BigStepLoop χ σ (.postTest body c) (.returnValue v) σbody
  | postTestNormalFalse {σ σbody σc : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .normal σbody →
      BigStepValue.CondValue χ σbody c false σc →
      BigStepLoop χ σ (.postTest body c) .normal σc
  | postTestContFalse {σ σbody σc : State} {body : ControlPlan} {c : CppCond} :
      BigStepPlan χ σ body .continueResult σbody →
      BigStepValue.CondValue χ σbody c false σc →
      BigStepLoop χ σ (.postTest body c) .normal σc
  | postTestNormalTrue {σ σbody σc σ' : State} {body : ControlPlan} {c : CppCond}
      {r : CtrlResult} :
      BigStepPlan χ σ body .normal σbody →
      BigStepValue.CondValue χ σbody c true σc →
      BigStepLoop χ σc (.postTest body c) r σ' →
      BigStepLoop χ σ (.postTest body c) r σ'
  | postTestContTrue {σ σbody σc σ' : State} {body : ControlPlan} {c : CppCond}
      {r : CtrlResult} :
      BigStepPlan χ σ body .continueResult σbody →
      BigStepValue.CondValue χ σbody c true σc →
      BigStepLoop χ σc (.postTest body c) r σ' →
      BigStepLoop χ σ (.postTest body c) r σ'
  | forFrame {σ σinit σ' : State}
      {init : CppForInit} {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan}
      {r : CtrlResult} :
      BigStepForInit χ σ init σinit →
      BigStepForRemainder χ σinit cond iter body r σ' →
      BigStepLoop χ σ (.forFrame init cond iter body) r σ'

/-- Finite execution of the reentry part of a `for` loop after the initializer has
already run. -/
inductive BigStepForRemainder (χ : KernelContext) :
    State → Option CppCond → CppForIter → ControlPlan → CtrlResult → State → Prop where
  | condFalse {σ σc : State} {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondFalse χ σ cond σc →
      BigStepForRemainder χ σ cond iter body .normal σc
  | bodyNormal {σ σc σbody σiter σ' : State}
      {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} {r : CtrlResult} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .normal σbody →
      BigStepForIter χ σbody iter σiter →
      BigStepForRemainder χ σiter cond iter body r σ' →
      BigStepForRemainder χ σ cond iter body r σ'
  | bodyCont {σ σc σbody σiter σ' : State}
      {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} {r : CtrlResult} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .continueResult σbody →
      BigStepForIter χ σbody iter σiter →
      BigStepForRemainder χ σiter cond iter body r σ' →
      BigStepForRemainder χ σ cond iter body r σ'
  | bodyBreak {σ σc σbody : State}
      {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .breakResult σbody →
      BigStepForRemainder χ σ cond iter body .normal σbody
  | bodyReturnVoid {σ σc σbody : State}
      {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body .returnVoid σbody →
      BigStepForRemainder χ σ cond iter body .returnVoid σbody
  | bodyReturnValue {σ σc σbody : State}
      {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan} {v : Value} :
      BigStepOptionalCondTrue χ σ cond σc →
      BigStepPlan χ σc body (.returnValue v) σbody →
      BigStepForRemainder χ σ cond iter body (.returnValue v) σbody

/-- Finite execution of an already-selected switch suffix. -/
inductive BigStepSwitchSuffix (χ : KernelContext) :
    State → SwitchPlanArmList → CtrlResult → State → Prop where
  | nil {σ : State} :
      BigStepSwitchSuffix χ σ .nil .normal σ
  | armNormal {σ σbody σ' : State} {label : SwitchLabel} {body : PlanBlock}
      {rest : SwitchPlanArmList} {r : CtrlResult} :
      BigStepBlock χ σ body .normal σbody →
      BigStepSwitchSuffix χ σbody rest r σ' →
      BigStepSwitchSuffix χ σ (.cons (.arm label body) rest) r σ'
  | armBreak {σ σbody : State} {label : SwitchLabel} {body : PlanBlock}
      {rest : SwitchPlanArmList} :
      BigStepBlock χ σ body .breakResult σbody →
      BigStepSwitchSuffix χ σ (.cons (.arm label body) rest) .normal σbody
  | armCont {σ σbody : State} {label : SwitchLabel} {body : PlanBlock}
      {rest : SwitchPlanArmList} :
      BigStepBlock χ σ body .continueResult σbody →
      BigStepSwitchSuffix χ σ (.cons (.arm label body) rest) .continueResult σbody
  | armReturnVoid {σ σbody : State} {label : SwitchLabel} {body : PlanBlock}
      {rest : SwitchPlanArmList} :
      BigStepBlock χ σ body .returnVoid σbody →
      BigStepSwitchSuffix χ σ (.cons (.arm label body) rest) .returnVoid σbody
  | armReturnValue {σ σbody : State} {label : SwitchLabel} {body : PlanBlock}
      {rest : SwitchPlanArmList} {v : Value} :
      BigStepBlock χ σ body (.returnValue v) σbody →
      BigStepSwitchSuffix χ σ (.cons (.arm label body) rest) (.returnValue v) σbody

end

end Cpp4
