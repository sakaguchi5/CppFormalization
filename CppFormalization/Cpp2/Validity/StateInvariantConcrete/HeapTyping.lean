import CppFormalization.Cpp2.RuntimeModel.RuntimeState

/-!
Runtime heap typing invariant shared by concrete validity and entry boundaries.

This file is deliberately below `Entry`: it only talks about the runtime heap and
stored value compatibility, and does not mention readiness or dynamic boundaries.
-/

namespace Cpp

/-- heap に入っている initialized value は cell の型に整合する。 -/
def heapInitializedValuesTyped (σ : State) : Prop :=
  ∀ a c v,
    σ.heap a = some c →
    c.value = some v →
    ValueCompat v c.ty

end Cpp
