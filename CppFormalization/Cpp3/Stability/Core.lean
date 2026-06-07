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

The proposition is an argument of the certificate rather than a hidden field.
This keeps the meaning of the certificate visible at the type level: a stability
certificate is always evidence for a particular proposition `P`. -/
structure StabilityCertificate
    (kind : Contracts.CertifiedFamily) (P : Prop) : Type where
  evidence : Contracts.Certified P

namespace StabilityCertificate

/-- Extract the evidence carried by a stability certificate. -/
def get {kind : Contracts.CertifiedFamily} {P : Prop}
    (h : StabilityCertificate kind P) : P :=
  h.evidence

end StabilityCertificate

universe u

/-- Generic low-level stable-boundary wrapper.

Most structured Stability files should prefer direct `source` + `target` fields.
This wrapper remains available only as glue vocabulary for registry-like handoff
points where a boundary and its visible certificate proposition must be carried
together. -/
structure StableBoundary (B : Type u) (P : Prop) : Type (max 1 u) where
  boundary : B
  certificate : StabilityCertificate .stabilityDerived P

namespace StableBoundary

/-- Project the boundary carried by a stable-boundary package. -/
def getBoundary {B : Type u} {P : Prop} (h : StableBoundary B P) : B :=
  h.boundary

/-- Project the stability certificate carried by a stable-boundary package. -/
def getCertificate {B : Type u} {P : Prop}
    (h : StableBoundary B P) : StabilityCertificate .stabilityDerived P :=
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
  "Stability exposes source and target runtime boundaries directly; generic certificates keep their proposition visible."

end Stability
end Cpp3
