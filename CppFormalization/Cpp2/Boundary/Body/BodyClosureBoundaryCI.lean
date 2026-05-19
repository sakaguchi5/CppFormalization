import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Boundary.Static.BodyStaticBoundaryCI
import CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary
import CppFormalization.Cpp2.Boundary.Adequacy.BodyAdequacyCI

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.Body.BodyClosureBoundaryCI

Assembled four-layer CI body boundary.

Canonical split:
- structural : shape / scopedness only
- static     : coarse typing + CI summary + root witness coherence
- dynamic    : concrete entry state/readiness
- adequacy   : soundness against the static profile
-/

structure BodyClosureBoundaryCI (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  static : BodyStaticBoundaryCI Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

structure BlockBodyClosureBoundaryCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  structural : BlockBodyStructuralBoundary Γ ss
  static : BlockBodyStaticBoundaryCI Γ ss
  dynamic : BlockBodyDynamicBoundary Γ σ ss
  adequacy : BlockBodyAdequacyCI Γ σ ss static.profile

def mkBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStructuralBoundary Γ st)
    (hst : BodyStaticBoundaryCI Γ st)
    (hd : BodyDynamicBoundary Γ σ st)
    (ha : BodyAdequacyCI Γ σ st hst.profile) :
    BodyClosureBoundaryCI Γ σ st :=
  { structural := hs
    static := hst
    dynamic := hd
    adequacy := ha }

def mkBlockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hs : BlockBodyStructuralBoundary Γ ss)
    (hst : BlockBodyStaticBoundaryCI Γ ss)
    (hd : BlockBodyDynamicBoundary Γ σ ss)
    (ha : BlockBodyAdequacyCI Γ σ ss hst.profile) :
    BlockBodyClosureBoundaryCI Γ σ ss :=
  { structural := hs
    static := hst
    dynamic := hd
    adequacy := ha }

end Cpp
