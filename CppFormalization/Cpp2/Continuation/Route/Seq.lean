import CppFormalization.Cpp2.Boundary.Static.BodyStaticBoundaryCI
import CppFormalization.Cpp2.Boundary.Adequacy.BodyAdequacyCI

namespace Cpp

/-!
# Seq selected route and tail adequacy payloads

Extracted aggressively from `Closure.Internal.SeqScaffoldRouteCI`.
This module owns the selected head-normal route object and the tail static /
adequacy payload attached to that route.

Long term, route core and tail adequacy can be separated further.  This file is
already outside `Closure/Internal`, so downstream continuation/contract modules
can depend on the route without importing the old seq closure scaffold file.
-/

/--
Static and adequacy payload for the tail of a sequence after an actual
left-normal route.

This is not a pure static object: it is indexed by the actual post-state and
contains semantic adequacy.  Therefore it belongs with the selected route /
continuation layer, not under `Static/Pure`.
-/
structure SeqTailStaticAdequacyCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  static : BodyStaticBoundaryCI Θ t
  adequacy : BodyAdequacyCI Θ σ1 t static.profile

/--
Normal-channel adequacy obligation for the tail after an actual left-normal
route.

This mirrors the left-side channel split.  Tail adequacy is path-sensitive, so
its support is indexed by the actual post-environment and post-state reached by
the left-normal execution.
-/
structure SeqTailNormalAdequacyCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt)
    (P : BodyControlProfile Θ t) : Type where
  normalSound :
    ∀ {σ2 : State} (_hstep : BigStepStmt σ1 t .normal σ2),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Θ t Δ},
        P.summary.normalOut = some out

/--
Return-channel adequacy obligation for the tail after an actual left-normal
route.
-/
structure SeqTailReturnAdequacyCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt)
    (P : BodyControlProfile Θ t) : Type where
  returnSound :
    ∀ {rv : Option Value} {σ2 : State}
      (_hstep : BigStepStmt σ1 t (.returnResult rv) σ2),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Θ t Δ},
        P.summary.returnOut = some out

/-- Type-level package for the two semantic adequacy channels of the tail. -/
structure SeqTailAdequacySupportCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt)
    (P : BodyControlProfile Θ t) : Type where
  normal : SeqTailNormalAdequacyCI Θ σ1 t P
  returned : SeqTailReturnAdequacyCI Θ σ1 t P

namespace SeqTailAdequacySupportCI

/-- Forget the channel-split tail support to ordinary `BodyAdequacyCI`. -/
noncomputable def toBodyAdequacyCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    {P : BodyControlProfile Θ t}
    (A : SeqTailAdequacySupportCI Θ σ1 t P) :
    BodyAdequacyCI Θ σ1 t P :=
  BodyAdequacyCI.ofWitness
    (normalWitness := by
      intro σ2 hstep
      let h := A.normal.normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩)
    (returnWitness := by
      intro rv σ2 hstep
      let h := A.returned.returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩)

end SeqTailAdequacySupportCI

/--
Type-level package selecting the tail static boundary together with channel-split
tail adequacy support after an actual left-normal route.
-/
structure SeqTailStaticAdequacyPayloadCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  static : BodyStaticBoundaryCI Θ t
  support : SeqTailAdequacySupportCI Θ σ1 t static.profile

/-- Compatibility package for the older tail scaffold API. -/
noncomputable def SeqTailStaticAdequacyPayloadCI.toStaticAdequacyCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    (p : SeqTailStaticAdequacyPayloadCI Θ σ1 t) :
    SeqTailStaticAdequacyCI Θ σ1 t :=
  { static := p.static
    adequacy := p.support.toBodyAdequacyCI }

/--
Core actual head-normal route through a sequence.

This is the mathematically/C++-natural route object: it records only that the
left statement `s` actually took the selected normal path from the pre-state to
the post-state, and which post-environment `Θ` that normal channel selects.

It deliberately does not contain tail static/adequacy/replay payloads.  Those
are continuation facts attached to this route, not the route itself.
-/
structure SeqHeadNormalRouteCoreCI
    (Γ : TypeEnv) (σ : State) (s t : CppStmt)
    (σ1 : State) (P : BodyControlProfile Γ s) : Type where
  Θ : TypeEnv
  hleft : HasTypeStmtCI .normalK Γ s Θ
  hprofile : P.summary.normalOut = some ⟨Θ, hleft⟩
  hstepLeft : BigStepStmt σ s .normal σ1

/--
Legacy full route through a sequence.

This extends the core actual route with the old bundled tail static/adequacy
payload.  New continuation/contract code should prefer
`SeqHeadNormalRouteCoreCI` plus explicit tail continuation facts.  This full
route remains as a compatibility wrapper for the older closure scaffold.
-/
structure SeqHeadNormalRouteCI
    (Γ : TypeEnv) (σ : State) (s t : CppStmt)
    (σ1 : State) (P : BodyControlProfile Γ s) : Type where
  Θ : TypeEnv
  hleft : HasTypeStmtCI .normalK Γ s Θ
  hprofile : P.summary.normalOut = some ⟨Θ, hleft⟩
  hstepLeft : BigStepStmt σ s .normal σ1
  tail : SeqTailStaticAdequacyPayloadCI Θ σ1 t

/-- Forget the legacy bundled tail payload and keep only the actual route core. -/
def SeqHeadNormalRouteCI.toCore
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqHeadNormalRouteCoreCI Γ σ s t σ1 P :=
  { Θ := route.Θ
    hleft := route.hleft
    hprofile := route.hprofile
    hstepLeft := route.hstepLeft }

end Cpp
