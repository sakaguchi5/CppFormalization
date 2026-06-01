import CppFormalization.Cpp2.Language.Outcome
import CppFormalization.Cpp2.RuntimeModel.RuntimeState

namespace Cpp

inductive ProgOutcome where
  | success  : ProgSuccess → State → ProgOutcome
  | diverges : ProgOutcome
  deriving Repr

end Cpp
