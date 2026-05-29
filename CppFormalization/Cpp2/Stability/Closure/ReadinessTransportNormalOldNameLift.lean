import CppFormalization.Cpp2.Stability.Closure.ReadinessTransportNormalOldNameTransport

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalOldNameLift

Stage 7 surface for lifting refined old-name transport to statements and blocks.

This is the mutual-recursive layer that should eventually consume the Stage-6
place/expression transport fragment and prove the statement/block old-name
transport goals.

The file is intentionally an interface layer, not an axiom.  It avoids claiming
the old unrestricted transport theorem.  The target still carries
`StmtDoesNotMentionIdent` / `BlockDoesNotMentionIdent`, which is the C++-honest
restriction needed for env-extending declarations.
-/

/- =========================================================
   1. Stage-7 statement/block old-name transport surface
   ========================================================= -/

/--
The statement/block part of env-extending old-name transport.

These fields match the old-name statement/block fields of
`ReadinessTransportNormalRefinedSurface`, but are kept as a separate fragment so
the proof can be built and audited independently from the full refined surface.
-/
structure ReadinessTransportNormalOldNameStmtBlockFragment : Type where
  declareObjOldStmtTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      DeclareObjOldNameStmtTransportGoal Γ σ σ' τ x ov

  declareObjOldBlockTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      DeclareObjOldNameBlockTransportGoal Γ σ σ' τ x ov

  declareRefOldStmtTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      DeclareRefOldNameStmtTransportGoal Γ σ σ' τ x p0

  declareRefOldBlockTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      DeclareRefOldNameBlockTransportGoal Γ σ σ' τ x p0

/--
Stage-7 audit bundle: the statement/block lift should be backed by the
place/expression fragment it is meant to lift.

The structure does not force the proof dependency mechanically yet, but it
records the intended architecture and prevents the statement/block fragment from
being mistaken for an unrestricted core replacement.
-/
structure ReadinessTransportNormalOldNameLiftProgram : Type where
  placeExpr : ReadinessTransportNormalOldNamePlaceExprFragment
  stmtBlock : ReadinessTransportNormalOldNameStmtBlockFragment

/-- Thin projection from a Stage-7 lift program to the statement/block fragment. -/
def ReadinessTransportNormalOldNameLiftProgram.toStmtBlock
    (P : ReadinessTransportNormalOldNameLiftProgram) :
    ReadinessTransportNormalOldNameStmtBlockFragment :=
  P.stmtBlock

end Cpp
