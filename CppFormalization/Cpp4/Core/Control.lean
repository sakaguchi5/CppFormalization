import CppFormalization.Cpp4.Core.Value

/-!
# CppFormalization.Cpp4.Core.Control

Control results and control contexts.  Reserved words such as `break` and
`continue` are lexical facts; whether they are usable is tracked here.
-/

namespace Cpp4

/-- Result channel for statement execution. -/
inductive CtrlResult where
  | normal
  | breakResult
  | continueResult
  | returnVoid
  | returnValue : Value → CtrlResult
  deriving DecidableEq, Repr

/-- Static/control context used by formation and typing. -/
structure ControlContext where
  loopDepth : Nat
  switchDepth : Nat
  returnType : Option CppType
  deriving Repr

namespace ControlContext

/-- Top-level context: no loop/switch and no function return channel. -/
def top : ControlContext where
  loopDepth := 0
  switchDepth := 0
  returnType := none

/-- Enter a loop body: `break` and `continue` are both enabled. -/
def enterLoop (κ : ControlContext) : ControlContext where
  loopDepth := κ.loopDepth + 1
  switchDepth := κ.switchDepth
  returnType := κ.returnType

/-- Enter a function body with the given return type. -/
def enterFunction (ret : CppType) : ControlContext where
  loopDepth := 0
  switchDepth := 0
  returnType := some ret

end ControlContext

/-- `break` is valid only in a loop or switch context. -/
def BreakAllowed (κ : ControlContext) : Prop :=
  κ.loopDepth > 0 ∨ κ.switchDepth > 0

/-- `continue` is valid only in a loop context. -/
def ContinueAllowed (κ : ControlContext) : Prop :=
  κ.loopDepth > 0

/-- `return` is valid only inside a function with a matching return channel. -/
def ReturnAllowed (κ : ControlContext) (τ : CppType) : Prop :=
  κ.returnType = some τ

end Cpp4
