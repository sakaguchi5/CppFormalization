import CppFormalization.Cpp2.Language.Types

namespace Cpp

inductive ProgSuccess where
  | normal
  | returned : Option Value → ProgSuccess
  deriving DecidableEq, Repr

end Cpp
