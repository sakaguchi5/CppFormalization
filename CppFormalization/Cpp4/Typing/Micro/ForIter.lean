import CppFormalization.Cpp4.Typing.Micro.Decl

/-!
# CppFormalization.Cpp4.Typing.Micro.ForIter

Micro typing for the restricted Cpp4 `for` iteration-expression surface.

The syntax deliberately excludes `break`, `continue`, and `return`; this file
therefore produces only an atom demand and no environment effect.
-/

namespace Cpp4

/-- Micro typing certificate for `for` iteration fragments. -/
structure ForIterTyping (Γ : TypeEnv) (iter : CppForIter) : Type where
  demand : AtomDemand
  formation : Prop
  evidence : formation

namespace ForIterTyping

/-- Empty iteration step. -/
def none (Γ : TypeEnv) : ForIterTyping Γ .none where
  demand := AtomDemand.skip
  formation := True
  evidence := trivial

/-- Expression iteration step. -/
def expr {Γ : TypeEnv} {s : CppExprStmt}
    (h : ExprStmtTyping Γ s) : ForIterTyping Γ (.expr s) where
  demand := h.demand
  formation := h.formation
  evidence := h.evidence

/-- Assignment iteration step. -/
def assign {Γ : TypeEnv} {a : CppAssign}
    (h : AssignTyping Γ a) : ForIterTyping Γ (.assign a) where
  demand := h.demand
  formation := h.formation
  evidence := h.evidence

end ForIterTyping

end Cpp4
