import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Block

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: statement replay

Statement replay is the main dynamic replay predicate for a seq tail.  It is
route-local and post-state oriented: it never states a global readiness
transport principle.
-/

/--
Route-local replay for a statement used as a seq tail.

The constructors mirror `StmtReadyConcrete`, but their expression/place inputs
are replay witnesses at the selected post-state.  Compound statements recurse on
replay, so the materialization theorem is a direct structural proof.
-/
inductive StmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    CppStmt → Prop where
  | skip :
      StmtReplay route .skip
  | exprStmt
      {e : ValExpr} {τ : CppType} :
      ValueReplay route e τ →
      StmtReplay route (.exprStmt e)
  | assign
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      PlaceReplay route p τ →
      ValueReplay route e τ →
      StmtReplay route (.assign p e)
  | declareObjNone
      {τ : CppType} {x : Ident} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      StmtReplay route (.declareObj τ x none)
  | declareObjSome
      {τ : CppType} {x : Ident} {e : ValExpr} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      ValueReplay route e τ →
      StmtReplay route (.declareObj τ x (some e))
  | declareRef
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh route.Θ x →
      PlaceReplay route p τ →
      StmtReplay route (.declareRef τ x p)
  | seq
      {u v : CppStmt} :
      StmtReplay route u →
      StmtReplay route v →
      StmtReplay route (.seq u v)
  | ite
      {c : ValExpr} {u v : CppStmt} :
      ValueReplay route c (.base .bool) →
      StmtReplay route u →
      StmtReplay route v →
      StmtReplay route (.ite c u v)
  | whileStmt
      {c : ValExpr} {body : CppStmt} :
      ValueReplay route c (.base .bool) →
      StmtReplay route body →
      StmtReplay route (.whileStmt c body)
  | block
      {ss : StmtBlock} :
      BlockReplay route ss →
      StmtReplay route (.block ss)
  | breakStmt :
      StmtReplay route .breakStmt
  | continueStmt :
      StmtReplay route .continueStmt
  | returnNone :
      StmtReplay route (.returnStmt none)
  | returnSome
      {e : ValExpr} {τ : CppType} :
      ValueReplay route e τ →
      StmtReplay route (.returnStmt (some e))

namespace StmtReplay

/-- Statement replay materializes concrete post-state statement readiness. -/
theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {st : CppStmt}
    (h : StmtReplay route st) :
    StmtReadyConcrete route.Θ σ1 st := by
  induction h with
  | skip =>
      exact StmtReadyConcrete.skip
  | exprStmt hvalue =>
      exact
        StmtReadyConcrete.exprStmt
          hvalue.hasValueType
          hvalue.ready
  | assign hplace hvalue =>
      exact
        StmtReadyConcrete.assign
          hplace.hasPlaceType
          hplace.ready
          hvalue.hasValueType
          hvalue.ready
  | declareObjNone hfresh hobj =>
      exact StmtReadyConcrete.declareObjNone hfresh hobj
  | declareObjSome hfresh hobj hvalue =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh
          hobj
          hvalue.hasValueType
          hvalue.ready
  | declareRef hfresh hplace =>
      exact
        StmtReadyConcrete.declareRef
          hfresh
          hplace.hasPlaceType
          hplace.ready
  | seq _hu _hv ihU ihV =>
      exact StmtReadyConcrete.seq ihU ihV
  | ite hc _hu _hv ihU ihV =>
      exact
        StmtReadyConcrete.ite
          hc.hasValueType
          hc.ready
          ihU
          ihV
  | whileStmt hc _hbody ihBody =>
      exact
        StmtReadyConcrete.whileStmt
          hc.hasValueType
          hc.ready
          ihBody
  | block hblock =>
      exact StmtReadyConcrete.block hblock.ready
  | breakStmt =>
      exact StmtReadyConcrete.breakStmt
  | continueStmt =>
      exact StmtReadyConcrete.continueStmt
  | returnNone =>
      exact StmtReadyConcrete.returnNone
  | returnSome hvalue =>
      exact
        StmtReadyConcrete.returnSome
          hvalue.hasValueType
          hvalue.ready

end StmtReplay

end SeqTailReplay2
end Cpp
