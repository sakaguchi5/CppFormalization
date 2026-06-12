import CppFormalization.Cpp4.Typing.Micro.Decl

/-!
# CppFormalization.Cpp4.Typing.Judgment.Plan.Atom

ControlPlan-level typing certificates for primitive atoms.

This layer repackages `Typing.Micro.AtomTyping` with the ordinary-name
environment effect and typed resource demand that the Plan judgment needs.
-/

namespace Cpp4

/-- A typed primitive atom as seen by the ControlPlan judgment.

Primitive declarations may extend the ordinary type environment; all other
primitive atoms leave it unchanged. -/
structure PlanAtomTyping (Γ : TypeEnv) (κ : ControlContext) (a : ControlAtom) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  atomTyping : AtomTyping Γ κ a
  demand : AtomDemand
  formation : Prop
  evidence : formation

namespace PlanAtomTyping

/-- Repackage a micro atom typing certificate for the plan layer. -/
def ofMicro {Γ : TypeEnv} {κ : ControlContext} {a : ControlAtom}
    (h : AtomTyping Γ κ a) : PlanAtomTyping Γ κ a :=
  match h with
  | .skip =>
      { target := Γ
        envEffect := TypeEnvEffect.id Γ
        atomTyping := .skip
        demand := AtomDemand.skip
        formation := True
        evidence := trivial }
  | .exprStmt hs =>
      { target := Γ
        envEffect := TypeEnvEffect.id Γ
        atomTyping := .exprStmt hs
        demand := hs.demand
        formation := hs.formation
        evidence := hs.evidence }
  | .assign ha =>
      { target := Γ
        envEffect := TypeEnvEffect.id Γ
        atomTyping := .assign ha
        demand := ha.demand
        formation := ha.formation
        evidence := ha.evidence }
  | .decl hd =>
      { target := hd.target
        envEffect := hd.envEffect
        atomTyping := .decl hd
        demand := hd.demand
        formation := hd.formation
        evidence := hd.evidence }
  | .jump hj =>
      { target := Γ
        envEffect := TypeEnvEffect.id Γ
        atomTyping := .jump hj
        demand := hj.demand
        formation := True
        evidence := trivial }

/-- Atom demand exposed by a plan-level atom certificate. -/
def atomDemand {Γ : TypeEnv} {κ : ControlContext} {a : ControlAtom}
    (h : PlanAtomTyping Γ κ a) : AtomDemand :=
  h.demand

end PlanAtomTyping

end Cpp4
