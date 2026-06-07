import CppFormalization.Cpp3.Boundary.All

/-!
# CppFormalization.Cpp3.Stability.Core

Core vocabulary for runtime-boundary stability.

`Boundary` says that a concrete state can enter a program point.  `Stability`
names the evidence that executing a selected effect/route leaves the next
required boundary available.  This layer still does not prove final soundness and
it does not perform continuation composition.
-/

namespace Cpp3
namespace Stability

/-- Explicit theorem-backed evidence for a stability fact.

The proposition is intentionally explicit: early files may carry a stability fact
as evidence, while later proof files can replace particular packages with actual
theorems. -/
structure StabilityCertificate (kind : Contracts.CertifiedFamily) : Type where
  proposition : Prop
  evidence : Contracts.Certified proposition

namespace StabilityCertificate

/-- Extract the evidence carried by a stability certificate. -/
def get {kind : Contracts.CertifiedFamily}
    (h : StabilityCertificate kind) : h.proposition :=
  h.evidence

end StabilityCertificate

universe u

/-- A boundary paired with theorem-backed stability evidence.

This is the generic shape consumed by later `Continuation` packages: a post-state
boundary plus the fact explaining why it remained available. -/
structure StableBoundary (B : Type u) : Type (max 1 u) where
  boundary : B
  certificate : StabilityCertificate .stabilityDerived

namespace StableBoundary

/-- Project the boundary carried by a stable-boundary package. -/
def getBoundary {B : Type u} (h : StableBoundary B) : B :=
  h.boundary

/-- Project the stability certificate carried by a stable-boundary package. -/
def getCertificate {B : Type u}
    (h : StableBoundary B) : StabilityCertificate .stabilityDerived :=
  h.certificate

end StableBoundary

/-- Generic preservation of a named runtime-boundary proposition.

Use this only as a low-level glue vocabulary.  Program-specific stability should
prefer the structured packages in the sibling files. -/
structure RuntimeBoundaryPreserved
    (kind : Contracts.ObligationFamily) (before after : Prop) : Type where
  contractKind : Contracts.ContractKind := .obligation kind
  evidence : Contracts.Requires (before → after)

namespace RuntimeBoundaryPreserved

/-- Apply a generic runtime-boundary preservation package. -/
def apply {kind : Contracts.ObligationFamily} {before after : Prop}
    (h : RuntimeBoundaryPreserved kind before after) (hb : before) : after :=
  h.evidence hb

end RuntimeBoundaryPreserved

/-- Marker for the adopted stability-layer policy. -/
def stabilityLayerPolicy : String :=
  "Stability explains why post-state runtime boundaries survive selected execution; Continuation and Soundness remain later layers."

end Stability
end Cpp3
