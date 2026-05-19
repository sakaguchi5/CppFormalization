import CppFormalization.Cpp2.Boundary.Body.BodyClosureBoundaryCI

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.Body.BodyReadyCI

Integrated ready/boundary presentation for function bodies and opened block
bodies.

This is a boundary object, not a closure-construction object.  It carries the
same four layers as `BodyClosureBoundaryCI`, but keeps the historical `ReadyCI`
name for callers that speak in entry-readiness terms.
-/

structure BodyReadyCI (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

structure BlockBodyReadyCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  structural : BlockBodyStructuralBoundary Γ ss
  static : BlockBodyStaticBoundaryCI Γ ss
  dynamic : BlockBodyDynamicBoundary Γ σ ss
  adequacy : BlockBodyAdequacyCI Γ σ ss static.profile

end Cpp
