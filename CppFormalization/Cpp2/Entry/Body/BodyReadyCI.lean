import CppFormalization.Cpp2.Closure.Package.BodyClosureBoundaryCI

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

def BlockBodyClosureBoundaryCI.toBlockBodyReadyCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyClosureBoundaryCI Γ σ ss) :
    BlockBodyReadyCI Γ σ ss :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

def BodyClosureBoundaryCI.toBodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    BodyReadyCI Γ σ st :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

def BodyReadyCI.toClosureBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  mkBodyClosureBoundaryCI h.structural h.static h.dynamic h.adequacy

end Cpp
