import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Entry.Body.BodyReadyCI
import CppFormalization.Cpp2.Static.Facts.Control.BodyReadyControlExclusionCI

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.Body

Full continuation boundaries.

A dynamic continuation boundary says that the continuation can start in a
post-state.  This file adds the static/profile/adequacy layers needed by the
closure route, without making "readiness transport" the public subject.

Transitional note:
`BodyStaticBoundaryCI` and `BodyAdequacyCI` currently live in
`Closure.Foundation`, so this module imports that layer.  The design intent is
still that callers talk about continuation boundaries rather than direct
transport obligations.
-/

/-- Full post-state continuation boundary for a statement. -/
structure StmtContinuationBoundaryCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  dynamic : StmtContinuationDynamicBoundary Γ σ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

namespace StmtContinuationBoundaryCI

def toBodyDynamicBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtContinuationBoundaryCI Γ σ st) :
    BodyDynamicBoundary Γ σ st :=
  h.dynamic.toBodyDynamicBoundary

def toBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtContinuationBoundaryCI Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  { structural := h.structural
    static := h.static
    dynamic := h.toBodyDynamicBoundary
    adequacy := h.adequacy }

def ofBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    StmtContinuationBoundaryCI Γ σ st :=
  { structural := h.structural
    static := h.static
    dynamic := StmtContinuationDynamicBoundary.ofBodyDynamicBoundary h.dynamic
    adequacy := h.adequacy }

def toBodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtContinuationBoundaryCI Γ σ st) :
    BodyReadyCI Γ σ st :=
  { structural := h.structural
    static := h.static
    dynamic := h.toBodyDynamicBoundary
    adequacy := h.adequacy }

def ofBodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    StmtContinuationBoundaryCI Γ σ st :=
  { structural := h.structural
    static := h.static
    dynamic := StmtContinuationDynamicBoundary.ofBodyDynamicBoundary h.dynamic
    adequacy := h.adequacy }

theorem postState
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtContinuationBoundaryCI Γ σ st) :
    ScopedTypedStateConcrete Γ σ :=
  h.dynamic.state

theorem ready
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtContinuationBoundaryCI Γ σ st) :
    StmtReadyConcrete Γ σ st :=
  h.dynamic.safe

end StmtContinuationBoundaryCI

/-- Full post-state continuation boundary for an opened block body.

This is the opened-block analogue of `BlockBodyClosureBoundaryCI`.
It is intentionally distinct from `BlockContinuationDynamicBoundary`, which is
for current-environment block tails such as the tail of `s :: ss`.
-/
structure OpenedBlockContinuationBoundaryCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  structural : BlockBodyStructuralBoundary Γ ss
  static : BlockBodyStaticBoundaryCI Γ ss
  dynamic : BlockBodyDynamicBoundary Γ σ ss
  adequacy : BlockBodyAdequacyCI Γ σ ss static.profile

namespace OpenedBlockContinuationBoundaryCI

def toBlockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : OpenedBlockContinuationBoundaryCI Γ σ ss) :
    BlockBodyClosureBoundaryCI Γ σ ss :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

def ofBlockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyClosureBoundaryCI Γ σ ss) :
    OpenedBlockContinuationBoundaryCI Γ σ ss :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

def toBlockBodyReadyCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : OpenedBlockContinuationBoundaryCI Γ σ ss) :
    BlockBodyReadyCI Γ σ ss :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

def ofBlockBodyReadyCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    OpenedBlockContinuationBoundaryCI Γ σ ss :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

end OpenedBlockContinuationBoundaryCI

end Cpp
