import CppFormalization.Cpp4.Core.Scope

/-!
# CppFormalization.Cpp4.Core.Lifetime

Lifetime vocabulary as a first-class resource concept.
-/

namespace Cpp4

inductive LifetimeStatus where
  | live
  | ended
  deriving DecidableEq, Repr

/-- Lifetime metadata attached to a runtime cell. -/
structure LifetimeInfo where
  owner : ScopeId
  status : LifetimeStatus
  deriving Repr

/-- A lifetime is live exactly when its status is `live`. -/
def LifetimeInfo.Live (lt : LifetimeInfo) : Prop :=
  lt.status = .live

/-- A lifetime has ended exactly when its status is `ended`. -/
def LifetimeInfo.Ended (lt : LifetimeInfo) : Prop :=
  lt.status = .ended

end Cpp4
