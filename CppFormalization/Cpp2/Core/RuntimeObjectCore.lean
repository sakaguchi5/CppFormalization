import CppFormalization.Cpp2.Core.RuntimeState

namespace Cpp

/-!
# Core.RuntimeObjectCore

Stable import surface for the low-level object-update core.

The raw definitions now live in `Core.RuntimeState`, because the legacy façade
`declareObjectState` is itself defined by the split standard form
`declareObjectStateWithNext σ τ x ov (σ.next + 1)`.

Projection and transport facts for primitive state updates live in
`Lemmas.RuntimeState`; projection and transport facts specific to
`setNext`, `declareObjectStateCore`, and `declareObjectStateWithNext` live in
`Lemmas.RuntimeObjectCore`.
-/

end Cpp
