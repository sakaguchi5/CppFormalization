import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Lemmas.ControlExclusion

namespace Cpp

/-!
# Closure.Foundation.BodyClosureBoundaryCI

四層を束ねた assembled CI boundary.

重要:
- これは primitive layer ではなく assembly である。
- structural / profile / dynamic / adequacy を一つに束ねるが、
  それぞれの責務は定義上すでに分離されている。
-/

/-- Assembled CI boundary for a top-level function body. -/
structure BodyClosureBoundaryCI (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  adequacy : BodyAdequacyCI Γ σ st profile

/-- Assembled CI boundary for an opened block body. -/
structure BlockBodyClosureBoundaryCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  structural : BlockBodyStructuralBoundary Γ ss
  profile : BlockBodyControlProfile Γ ss
  dynamic : BlockBodyDynamicBoundary Γ σ ss
  adequacy : BlockBodyAdequacyCI Γ σ ss profile

/-- Constructor-style helper for readability at use sites. -/
def mkBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStructuralBoundary Γ st)
    (hp : BodyControlProfile Γ st)
    (hd : BodyDynamicBoundary Γ σ st)
    (ha : BodyAdequacyCI Γ σ st hp) :
    BodyClosureBoundaryCI Γ σ st :=
  { structural := hs
    profile := hp
    dynamic := hd
    adequacy := ha }

/-- Constructor-style helper for opened block bodies. -/
def mkBlockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hs : BlockBodyStructuralBoundary Γ ss)
    (hp : BlockBodyControlProfile Γ ss)
    (hd : BlockBodyDynamicBoundary Γ σ ss)
    (ha : BlockBodyAdequacyCI Γ σ ss hp) :
    BlockBodyClosureBoundaryCI Γ σ ss :=
  { structural := hs
    profile := hp
    dynamic := hd
    adequacy := ha }

/-- At a top-level assembled CI boundary, unresolved break is excluded. -/
theorem break_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .breakResult σ' := by
  intro σ' hstep
  exact stmt_break_not_scoped hstep h.structural.breakScoped

/-- At a top-level assembled CI boundary, unresolved continue is excluded. -/
theorem continue_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .continueResult σ' := by
  intro σ' hstep
  exact stmt_continue_not_scoped hstep h.structural.continueScoped

/-- Top-level abrupt control is excluded at an assembled CI function-body boundary. -/
theorem top_level_abrupt_excluded_from_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyClosureBoundaryCI Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro h
  constructor
  · exact break_excluded_from_bodyClosureBoundaryCI h
  · exact continue_excluded_from_bodyClosureBoundaryCI h

/-- Opened block-body assembled CI boundaries exclude unresolved abrupt exits. -/
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
