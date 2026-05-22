import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Basic

namespace Cpp
namespace WhileClosure2

/-!
# Route-independent replay core

This is the route-independent core extracted from the successful seq-tail
experiment.  It is intentionally not indexed by a seq route.  A seq tail, cons
tail, or while backedge can all instantiate it by choosing the relevant
post-environment `Γ` and post-state `σ`.
-/

/-- Replay witness for a place at a concrete environment/state pair. -/
inductive PlaceReplayAt (Γ : TypeEnv) (σ : State) :
    PlaceExpr → CppType → Prop where
  | varObject
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl Γ x = some (.object τ) →
      lookupBinding σ x = some (.object τ a) →
      CellLiveTyped σ a τ →
      PlaceReplayAt Γ σ (.var x) τ
  | varRef
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl Γ x = some (.ref τ) →
      lookupBinding σ x = some (.ref τ a) →
      CellLiveTyped σ a τ →
      PlaceReplayAt Γ σ (.var x) τ
  | deref
      {e : ValExpr} {τ : CppType} {a : Nat} :
      PtrValueReadyAt Γ σ e τ a →
      CellLiveTyped σ a τ →
      PlaceReplayAt Γ σ (.deref e) τ

namespace PlaceReplayAt

theorem hasPlaceType
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType}
    (h : PlaceReplayAt Γ σ p τ) :
    HasPlaceType Γ p τ := by
  cases h with
  | varObject hdecl _hbind _hlive =>
      exact HasPlaceType.var hdecl
  | varRef hdecl _hbind _hlive =>
      exact HasPlaceType.var hdecl
  | deref hptr _hlive =>
      exact HasPlaceType.deref hptr.1

theorem ready
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType}
    (h : PlaceReplayAt Γ σ p τ) :
    PlaceReadyConcrete Γ σ p τ := by
  cases h with
  | varObject hdecl hbind hlive =>
      exact PlaceReadyConcrete.varObject hdecl hbind hlive
  | varRef hdecl hbind hlive =>
      exact PlaceReadyConcrete.varRef hdecl hbind hlive
  | deref hptr hlive =>
      exact PlaceReadyConcrete.deref hptr hlive

end PlaceReplayAt

/-- Replay witness for a value expression at a concrete environment/state pair. -/
inductive ValueReplayAt (Γ : TypeEnv) (σ : State) :
    ValExpr → CppType → Prop where
  | litBool {b : Bool} :
      ValueReplayAt Γ σ (.litBool b) (.base .bool)
  | litInt {n : Int} :
      ValueReplayAt Γ σ (.litInt n) (.base .int)
  | load
      {p : PlaceExpr} {τ : CppType} :
      PlaceReplayAt Γ σ p τ →
      (∃ a, BigStepPlace σ p a ∧ CellReadableTyped σ a τ) →
      ValueReplayAt Γ σ (.load p) τ
  | addrOf
      {p : PlaceExpr} {τ : CppType} :
      PlaceReplayAt Γ σ p τ →
      ValueReplayAt Γ σ (.addrOf p) (.ptr τ)
  | add
      {e₁ e₂ : ValExpr} :
      ValueReplayAt Γ σ e₁ (.base .int) →
      ValueReplayAt Γ σ e₂ (.base .int) →
      ValueReplayAt Γ σ (.add e₁ e₂) (.base .int)
  | sub
      {e₁ e₂ : ValExpr} :
      ValueReplayAt Γ σ e₁ (.base .int) →
      ValueReplayAt Γ σ e₂ (.base .int) →
      ValueReplayAt Γ σ (.sub e₁ e₂) (.base .int)
  | mul
      {e₁ e₂ : ValExpr} :
      ValueReplayAt Γ σ e₁ (.base .int) →
      ValueReplayAt Γ σ e₂ (.base .int) →
      ValueReplayAt Γ σ (.mul e₁ e₂) (.base .int)
  | eq
      {e₁ e₂ : ValExpr} {τ : CppType} :
      ValueReplayAt Γ σ e₁ τ →
      ValueReplayAt Γ σ e₂ τ →
      ValueReplayAt Γ σ (.eq e₁ e₂) (.base .bool)
  | lt
      {e₁ e₂ : ValExpr} :
      ValueReplayAt Γ σ e₁ (.base .int) →
      ValueReplayAt Γ σ e₂ (.base .int) →
      ValueReplayAt Γ σ (.lt e₁ e₂) (.base .bool)
  | not
      {e : ValExpr} :
      ValueReplayAt Γ σ e (.base .bool) →
      ValueReplayAt Γ σ (.not e) (.base .bool)

namespace ValueReplayAt

theorem hasValueType
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
    (h : ValueReplayAt Γ σ e τ) :
    HasValueType Γ e τ := by
  induction h with
  | litBool =>
      exact HasValueType.litBool
  | litInt =>
      exact HasValueType.litInt
  | load hplace _hread =>
      exact HasValueType.load hplace.hasPlaceType
  | addrOf hplace =>
      exact HasValueType.addrOf hplace.hasPlaceType
  | add _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.add ih₁ ih₂
  | sub _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.sub ih₁ ih₂
  | mul _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.mul ih₁ ih₂
  | eq _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.eq ih₁ ih₂
  | lt _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.lt ih₁ ih₂
  | not _h ih =>
      exact HasValueType.not ih

theorem ready
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
    (h : ValueReplayAt Γ σ e τ) :
    ExprReadyConcrete Γ σ e τ := by
  induction h with
  | litBool =>
      exact ExprReadyConcrete.litBool
  | litInt =>
      exact ExprReadyConcrete.litInt
  | load hplace hread =>
      exact ExprReadyConcrete.load hplace.ready hread
  | addrOf hplace =>
      exact ExprReadyConcrete.addrOf hplace.ready
  | add _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.add ih₁ ih₂
  | sub _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.sub ih₁ ih₂
  | mul _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.mul ih₁ ih₂
  | eq _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.eq ih₁ ih₂
  | lt _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.lt ih₁ ih₂
  | not _h ih =>
      exact ExprReadyConcrete.not ih

end ValueReplayAt

/--
Replay witness for a block tail in the current/open block scope.

The `cons` constructor deliberately takes the head statement readiness directly
under pushed scopes.  This keeps the first clean-room scaffold small; later this
can be refined into a fully recursive block replay core.
-/
inductive BlockReplayAt (Γ : TypeEnv) (σ : State) :
    StmtBlock → Prop where
  | nil :
      BlockReplayAt Γ σ .nil
  | cons
      {st : CppStmt} {ss : StmtBlock} :
      StmtReadyConcrete (pushTypeScope Γ) (pushScope σ) st →
      BlockReplayAt Γ σ ss →
      BlockReplayAt Γ σ (.cons st ss)

namespace BlockReplayAt

theorem ready
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockReplayAt Γ σ ss) :
    BlockReadyConcrete (pushTypeScope Γ) (pushScope σ) ss := by
  induction h with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hst _hss ih =>
      exact BlockReadyConcrete.cons hst ih

end BlockReplayAt

/-- Replay witness for a statement at a concrete environment/state pair. -/
inductive StmtReplayAt (Γ : TypeEnv) (σ : State) :
    CppStmt → Prop where
  | skip :
      StmtReplayAt Γ σ .skip
  | breakStmt :
      StmtReplayAt Γ σ .breakStmt
  | continueStmt :
      StmtReplayAt Γ σ .continueStmt
  | returnNone :
      StmtReplayAt Γ σ (.returnStmt none)
  | exprStmt
      {e : ValExpr} {τ : CppType} :
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.exprStmt e)
  | returnSome
      {e : ValExpr} {τ : CppType} :
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.returnStmt (some e))
  | declareObjNone
      {τ : CppType} {x : Ident} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      StmtReplayAt Γ σ (.declareObj τ x none)
  | declareObjSome
      {τ : CppType} {x : Ident} {e : ValExpr} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.declareObj τ x (some e))
  | declareRef
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh Γ x →
      PlaceReplayAt Γ σ p τ →
      StmtReplayAt Γ σ (.declareRef τ x p)
  | assign
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      PlaceReplayAt Γ σ p τ →
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.assign p e)
  | seq
      {u v : CppStmt} :
      StmtReplayAt Γ σ u →
      StmtReplayAt Γ σ v →
      StmtReplayAt Γ σ (.seq u v)
  | ite
      {c : ValExpr} {u v : CppStmt} :
      ValueReplayAt Γ σ c (.base .bool) →
      StmtReplayAt Γ σ u →
      StmtReplayAt Γ σ v →
      StmtReplayAt Γ σ (.ite c u v)
  | whileStmt
      {c : ValExpr} {body : CppStmt} :
      ValueReplayAt Γ σ c (.base .bool) →
      StmtReplayAt Γ σ body →
      StmtReplayAt Γ σ (.whileStmt c body)
  | block
      {ss : StmtBlock} :
      BlockReplayAt Γ σ ss →
      StmtReplayAt Γ σ (.block ss)

namespace StmtReplayAt

theorem ready
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtReplayAt Γ σ st) :
    StmtReadyConcrete Γ σ st := by
  induction h with
  | skip =>
      exact StmtReadyConcrete.skip
  | breakStmt =>
      exact StmtReadyConcrete.breakStmt
  | continueStmt =>
      exact StmtReadyConcrete.continueStmt
  | returnNone =>
      exact StmtReadyConcrete.returnNone
  | exprStmt hvalue =>
      exact StmtReadyConcrete.exprStmt hvalue.hasValueType hvalue.ready
  | returnSome hvalue =>
      exact StmtReadyConcrete.returnSome hvalue.hasValueType hvalue.ready
  | declareObjNone hfresh hobj =>
      exact StmtReadyConcrete.declareObjNone hfresh hobj
  | declareObjSome hfresh hobj hvalue =>
      exact
        StmtReadyConcrete.declareObjSome
          hfresh hobj hvalue.hasValueType hvalue.ready
  | declareRef hfresh hplace =>
      exact
        StmtReadyConcrete.declareRef
          hfresh hplace.hasPlaceType hplace.ready
  | assign hplace hvalue =>
      exact
        StmtReadyConcrete.assign
          hplace.hasPlaceType hplace.ready hvalue.hasValueType hvalue.ready
  | seq _hu _hv ihU ihV =>
      exact StmtReadyConcrete.seq ihU ihV
  | ite hc _hu _hv ihU ihV =>
      exact
        StmtReadyConcrete.ite
          hc.hasValueType hc.ready ihU ihV
  | whileStmt hc _hbody ihBody =>
      exact
        StmtReadyConcrete.whileStmt
          hc.hasValueType hc.ready ihBody
  | block hblock =>
      exact StmtReadyConcrete.block hblock.ready

end StmtReplayAt

end WhileClosure2
end Cpp
