import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyStaticBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Lemmas.ControlExclusion

namespace Cpp

/-!
# Closure.Foundation.BodyClosureBoundaryCI

Assembled CI boundary after the static-layer redesign.

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

theorem break_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .breakResult σ' := by
  intro σ' hstep
  exact stmt_break_not_scoped hstep h.structural.breakScoped

theorem continue_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .continueResult σ' := by
  intro σ' hstep
  exact stmt_continue_not_scoped hstep h.structural.continueScoped

theorem top_level_abrupt_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyClosureBoundaryCI Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro h
  constructor
  · exact break_excluded_from_bodyClosureBoundaryCI h
  · exact continue_excluded_from_bodyClosureBoundaryCI h

theorem top_level_abrupt_excluded_from_blockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss →
    ¬ BigStepBlock σ ss .breakResult σ' ∧ ¬ BigStepBlock σ ss .continueResult σ' := by
  intro h
  constructor
  · intro hbreak
    exact no_top_break_from_scoped_block h.structural.breakScoped hbreak
  · intro hcont
    exact no_top_continue_from_scoped_block h.structural.continueScoped hcont

end Cpp
