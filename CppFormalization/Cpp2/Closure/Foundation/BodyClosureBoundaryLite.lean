import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundaryLite
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BlockBodyDynamicBoundaryLite
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfileLite
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyLite
import CppFormalization.Cpp2.Lemmas.ControlExclusion

namespace Cpp

/-!
# Closure.Foundation.BodyClosureBoundaryLite

E-lite の assembled boundary.

方針:
- top-level function body では existing `BodyDynamicBoundary` をそのまま使う。
- opened block body では outer Γ ではなく local env `Λ` を直接 index する
  `BlockBodyDynamicBoundaryLite` を使う。
- これにより block body の head normal 後に local env `Δ` へ honest に遷移できる。
-/


/-- Assembled lite boundary for a top-level function body. -/
structure BodyClosureBoundaryLite (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundaryLite st
  profile : StmtBodyProfileLite Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  adequacy : StmtBodyAdequacyLite Γ σ profile

/-- Assembled lite boundary for an opened block body, indexed by the current local env. -/
structure BlockBodyClosureBoundaryLite (Λ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  structural : BlockBodyStructuralBoundaryLite ss
  profile : BlockBodyProfileLite Λ ss
  dynamic : BlockBodyDynamicBoundaryLite Λ σ ss
  adequacy : BlockBodyAdequacyLite Λ σ profile

/-- Constructor-style helper for readability at use sites. -/
def mkBodyClosureBoundaryLite
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStructuralBoundaryLite st)
    (hp : StmtBodyProfileLite Γ st)
    (hd : BodyDynamicBoundary Γ σ st)
    (ha : StmtBodyAdequacyLite Γ σ hp) :
    BodyClosureBoundaryLite Γ σ st :=
  { structural := hs
    profile := hp
    dynamic := hd
    adequacy := ha }

/-- Constructor-style helper for opened block bodies. -/
def mkBlockBodyClosureBoundaryLite
    {Λ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hs : BlockBodyStructuralBoundaryLite ss)
    (hp : BlockBodyProfileLite Λ ss)
    (hd : BlockBodyDynamicBoundaryLite Λ σ ss)
    (ha : BlockBodyAdequacyLite Λ σ hp) :
    BlockBodyClosureBoundaryLite Λ σ ss :=
  { structural := hs
    profile := hp
    dynamic := hd
    adequacy := ha }

/-- At a top-level assembled lite boundary, unresolved break is excluded. -/
theorem break_excluded_from_bodyClosureBoundaryLite
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryLite Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .breakResult σ' := by
  intro σ' hstep
  exact stmt_break_not_scoped hstep h.structural.breakScoped

/-- At a top-level assembled lite boundary, unresolved continue is excluded. -/
theorem continue_excluded_from_bodyClosureBoundaryLite
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryLite Γ σ st) :
    ∀ {σ' : State}, ¬ BigStepStmt σ st .continueResult σ' := by
  intro σ' hstep
  exact stmt_continue_not_scoped hstep h.structural.continueScoped

/-- Top-level abrupt control is excluded at an assembled lite function-body boundary. -/
theorem top_level_abrupt_excluded_from_bodyClosureBoundaryLite
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyClosureBoundaryLite Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro h
  constructor
  · exact break_excluded_from_bodyClosureBoundaryLite h
  · exact continue_excluded_from_bodyClosureBoundaryLite h

/-- Opened block-body lite boundaries exclude unresolved abrupt exits. -/
theorem top_level_abrupt_excluded_from_blockBodyClosureBoundaryLite
    {Λ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryLite Λ σ ss →
    ¬ BigStepBlock σ ss .breakResult σ' ∧ ¬ BigStepBlock σ ss .continueResult σ' := by
  intro h
  constructor
  · intro hbreak
    exact no_top_break_from_scoped_block h.structural.breakScoped hbreak
  · intro hcont
    exact no_top_continue_from_scoped_block h.structural.continueScoped hcont

end Cpp
