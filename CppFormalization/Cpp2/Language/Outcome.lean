import CppFormalization.Cpp2.RuntimeModel.RuntimeState

namespace Cpp

inductive ProgSuccess where
  | normal
  | returned : Option Value → ProgSuccess
  deriving DecidableEq, Repr

inductive ProgOutcome where
  | success  : ProgSuccess → State → ProgOutcome
  | diverges : ProgOutcome
  deriving Repr

end Cpp
