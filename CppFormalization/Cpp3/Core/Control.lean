import CppFormalization.Cpp3.Core.Types

/-!
Core control-channel vocabulary.

`CtrlResult` is the runtime control result of statement/block execution.
`ControlKind` is the matching static/control-index used by control-sensitive typing.
Neither belongs to a particular proof layer.
-/

namespace Cpp3

inductive CtrlResult where
  | normal
  | breakResult
  | continueResult
  | returnResult : Option Value → CtrlResult
  deriving DecidableEq, Repr

inductive ControlKind where
  | normalK
  | breakK
  | continueK
  | returnK
  deriving DecidableEq, Repr

end Cpp3
