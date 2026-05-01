import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI

namespace Cpp

/-!
# Closure.Internal.IteBranchAdequacyAssetsCI

The ite branch adequacy witness route is now defined in
`FunctionBodyCaseSplitCI.lean`, because that file owns the live ite branch
runtime-decision surfaces.

This file is intentionally a thin secondary-assets import surface.  Keeping it
definition-free avoids an import cycle and avoids duplicate declarations.
-/

end Cpp
