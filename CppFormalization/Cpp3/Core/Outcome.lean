import CppFormalization.Cpp3.Core.RuntimeState

namespace Cpp3

inductive ProgSuccess where
  | normal
  | returned : Option Value → ProgSuccess
  deriving DecidableEq, Repr

inductive ProgOutcome where
  | success  : ProgSuccess → State → ProgOutcome
  | diverges : ProgOutcome
  deriving Repr

end Cpp3
