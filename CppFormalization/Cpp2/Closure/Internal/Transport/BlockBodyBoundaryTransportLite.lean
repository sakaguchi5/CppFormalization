import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryLite
import CppFormalization.Cpp2.Closure.Foundation.ReadinessInversions
import CppFormalization.Cpp2.Closure.Transitions.Scope.OpenPreservation

namespace Cpp
namespace BlockBodyBoundaryTransportLite

/-!
# Closure.Internal.Transport.BlockBodyBoundaryTransportLite

E-lite block clause の opened-body bridge.

役割:
- top-level `.block ss` の lite boundary から、
  opened scope の下の `BlockBodyClosureBoundaryLite (pushTypeScope Γ) σ' ss`
  を honest に再構成する。
- ここではまだ `CloseScope` をまたぐ statement-level wrapper は扱わない。
-/


/-! ## structural transport -/

/-- Parent block structural boundary から opened block-body lite structural boundary を再構成する。 -/
theorem blockBodyStructuralLite_of_parent
     {ss : StmtBlock}
    (hs : BodyStructuralBoundaryLite (.block ss)) :
    BlockBodyStructuralBoundaryLite ss := by
  have hwf : WellFormedBlock ss := by
    simpa [WellFormedStmt] using hs.wf
  have hbreak : BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScoped, BreakWellScopedAt] using hs.breakScoped
  have hcont : ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScoped, ContinueWellScopedAt] using hs.continueScoped
  exact
    { wf := hwf
      breakScoped := hbreak
      continueScoped := hcont }

/-! ## dynamic transport -/

/-- Parent block dynamic boundary と `OpenScope` から opened block-body lite dynamic boundary を再構成する。 -/
theorem blockBodyDynamicLite_of_parent_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hd : BodyDynamicBoundary Γ σ (.block ss))
    (hopen : OpenScope σ σ') :
    BlockBodyDynamicBoundaryLite (pushTypeScope Γ) σ' ss := by
  refine
    { state := ?_
      safe := ?_ }
  · exact openScope_preserves_scoped_typed_state_concrete hd.state hopen
  · cases hopen
    exact stmtReadyConcrete_block_body hd.safe

/-! ## adequacy projection -/

/-- Canonical block node から opened block-body adequacy family を適用する。 -/
def blockBodyAdequacyLite_of_parent_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    {P : BlockBodyProfileLite (pushTypeScope Γ) ss}
    (ha : StmtBodyAdequacyLite Γ σ (.block P))
    (hopen : OpenScope σ σ') :
    BlockBodyAdequacyLite (pushTypeScope Γ) σ' P := by
  cases ha with
  | block hbody =>
      exact hbody hopen

/-! ## assembled opened block-body boundary -/

/-- Canonical block node を直接受け取る opened block-body boundary constructor. -/
def blockBodyBoundaryLite_of_parent_opened_mk
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    {P : BlockBodyProfileLite (pushTypeScope Γ) ss}
    (hs : BodyStructuralBoundaryLite (.block ss))
    (hd : BodyDynamicBoundary Γ σ (.block ss))
    (ha : StmtBodyAdequacyLite Γ σ (.block P))
    (hopen : OpenScope σ σ') :
    BlockBodyClosureBoundaryLite (pushTypeScope Γ) σ' ss := by
  exact
    mkBlockBodyClosureBoundaryLite
      (blockBodyStructuralLite_of_parent hs)
      P
      (blockBodyDynamicLite_of_parent_opened hd hopen)
      (blockBodyAdequacyLite_of_parent_opened ha hopen)

/-- Assembled boundary 版の opened block-body bridge. -/
def blockBodyBoundaryLite_of_bodyClosureBoundaryLite_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    {P : BlockBodyProfileLite (pushTypeScope Γ) ss}
    (h : BodyClosureBoundaryLite Γ σ (.block ss))
    (hprof : h.profile = .block P)
    (hopen : OpenScope σ σ') :
    BlockBodyClosureBoundaryLite (pushTypeScope Γ) σ' ss := by
  cases h with
  | mk hs hp hd ha =>
      cases hprof
      exact blockBodyBoundaryLite_of_parent_opened_mk
        (hs := hs) (hd := hd) (ha := ha) hopen

end BlockBodyBoundaryTransportLite
end Cpp
