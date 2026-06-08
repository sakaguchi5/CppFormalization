import CppFormalization.Cpp3.Stability.All

/-!
# CppFormalization.Cpp3.Continuation.Core

Core vocabulary for continuation handoff.

`Boundary` says that a concrete state can enter a program point.
`Stability` says that a selected route leaves the target boundary available.
`Continuation` consumes that target boundary as the next executable surface.

This layer still does not prove final soundness.  It only makes the handoff from a
selected route to the next program point explicit.
-/

namespace Cpp3
namespace Continuation

/-- Explicit evidence for a continuation-facing proposition.

The proposition is visible at the type level, following the refined
`StabilityCertificate` pattern. -/
structure ContinuationCertificate (P : Prop) : Type where
  evidence : Contracts.Certified P

namespace ContinuationCertificate

/-- Extract the evidence carried by a continuation certificate. -/
def get {P : Prop} (h : ContinuationCertificate P) : P :=
  h.evidence

end ContinuationCertificate

universe u v

/-- A generic continuation handoff from a source package to a target package.

Structured continuation files should prefer their statement-specific packages;
this low-level wrapper is only glue vocabulary for registries and later proof
handoffs. -/
structure ContinuationHandoff
    (Source : Type u) (Target : Type v) (P : Prop) : Type (max u v) where
  source : Source
  target : Target
  certificate : ContinuationCertificate P

namespace ContinuationHandoff

/-- Project the source carried by a continuation handoff. -/
def getSource {Source : Type u} {Target : Type v} {P : Prop}
    (h : ContinuationHandoff Source Target P) : Source :=
  h.source

/-- Project the target carried by a continuation handoff. -/
def getTarget {Source : Type u} {Target : Type v} {P : Prop}
    (h : ContinuationHandoff Source Target P) : Target :=
  h.target

end ContinuationHandoff

/-- Marker for the adopted continuation-layer policy. -/
def continuationLayerPolicy : String :=
  "Continuation consumes Stability target boundaries; Soundness remains a later layer."

end Continuation
end Cpp3
