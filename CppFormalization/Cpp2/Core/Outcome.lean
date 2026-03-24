import CppFormalization.Cpp2.Core.Syntax
import CppFormalization.Cpp2.Core.RuntimeState

namespace Cpp

inductive CtrlResult where
  | normal
  | breakResult
  | continueResult
  | returnResult : Option Value → CtrlResult
  deriving DecidableEq, Repr

inductive ProgSuccess where
  | normal
  | returned : Option Value → ProgSuccess
  deriving DecidableEq, Repr

inductive ProgOutcome where
  | success  : ProgSuccess → State → ProgOutcome
  | diverges : ProgOutcome
  deriving Repr

end Cpp
