import CppFormalization.Cpp2.Continuation.Compound.Basic

namespace Cpp
namespace CompoundContinuation

/-!
# Route-independent replay core

Replay witnesses are post-state facts.  They are not global readiness transport
principles.  A seq tail, a cons tail, or a while backedge can instantiate this
core by choosing the relevant post-environment and post-state.

Important implementation point:
`StmtReplayAt` and `BlockReplayAt` use `Γ` and `σ` as indices, not as fixed
mutual-inductive parameters.  This is necessary because statement replay for
`.block ss` moves to the opened block environment
`pushTypeScope Γ, pushScope σ`.
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

mutual

/-- Replay witness for a statement at a concrete environment/state pair. -/
inductive StmtReplayAt : TypeEnv → State → CppStmt → Prop where
  | skip {Γ : TypeEnv} {σ : State} :
      StmtReplayAt Γ σ .skip
  | breakStmt {Γ : TypeEnv} {σ : State} :
      StmtReplayAt Γ σ .breakStmt
  | continueStmt {Γ : TypeEnv} {σ : State} :
      StmtReplayAt Γ σ .continueStmt
  | returnNone {Γ : TypeEnv} {σ : State} :
      StmtReplayAt Γ σ (.returnStmt none)
  | exprStmt
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.exprStmt e)
  | returnSome
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.returnStmt (some e))
  | declareObjNone
      {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      StmtReplayAt Γ σ (.declareObj τ x none)
  | declareObjSome
      {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident} {e : ValExpr} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.declareObj τ x (some e))
  | declareRef
      {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh Γ x →
      PlaceReplayAt Γ σ p τ →
      StmtReplayAt Γ σ (.declareRef τ x p)
  | assign
      {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      PlaceReplayAt Γ σ p τ →
      ValueReplayAt Γ σ e τ →
      StmtReplayAt Γ σ (.assign p e)
  | seq
      {Γ : TypeEnv} {σ : State} {u v : CppStmt} :
      StmtReplayAt Γ σ u →
      StmtReplayAt Γ σ v →
      StmtReplayAt Γ σ (.seq u v)
  | ite
      {Γ : TypeEnv} {σ : State} {c : ValExpr} {u v : CppStmt} :
      ValueReplayAt Γ σ c (.base .bool) →
      StmtReplayAt Γ σ u →
      StmtReplayAt Γ σ v →
      StmtReplayAt Γ σ (.ite c u v)
  | whileStmt
      {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
      ValueReplayAt Γ σ c (.base .bool) →
      StmtReplayAt Γ σ body →
      StmtReplayAt Γ σ (.whileStmt c body)
  | block
      {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
      BlockReplayAt (pushTypeScope Γ) (pushScope σ) ss →
      StmtReplayAt Γ σ (.block ss)

/-- Replay witness for a block tail in the current/open block environment. -/
inductive BlockReplayAt : TypeEnv → State → StmtBlock → Prop where
  | nil {Γ : TypeEnv} {σ : State} :
      BlockReplayAt Γ σ .nil
  | cons
      {Γ : TypeEnv} {σ : State} {st : CppStmt} {ss : StmtBlock} :
      StmtReplayAt Γ σ st →
      BlockReplayAt Γ σ ss →
      BlockReplayAt Γ σ (.cons st ss)

end

mutual

theorem stmtReplayAt_ready
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtReplayAt Γ σ st) :
    StmtReadyConcrete Γ σ st := by
  cases h with
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
  | seq hu hv =>
      exact StmtReadyConcrete.seq (stmtReplayAt_ready hu) (stmtReplayAt_ready hv)
  | ite hc hu hv =>
      exact
        StmtReadyConcrete.ite
          hc.hasValueType hc.ready
          (stmtReplayAt_ready hu)
          (stmtReplayAt_ready hv)
  | whileStmt hc hbody =>
      exact
        StmtReadyConcrete.whileStmt
          hc.hasValueType hc.ready
          (stmtReplayAt_ready hbody)
  | block hblock =>
      exact StmtReadyConcrete.block (blockReplayAt_ready hblock)

theorem blockReplayAt_ready
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockReplayAt Γ σ ss) :
    BlockReadyConcrete Γ σ ss := by
  cases h with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hst hss =>
      exact
        BlockReadyConcrete.cons
          (stmtReplayAt_ready hst)
          (blockReplayAt_ready hss)

end

namespace StmtReplayAt

theorem ready
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtReplayAt Γ σ st) :
    StmtReadyConcrete Γ σ st :=
  stmtReplayAt_ready h

end StmtReplayAt

namespace BlockReplayAt

theorem ready
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockReplayAt Γ σ ss) :
    BlockReadyConcrete Γ σ ss :=
  blockReplayAt_ready h

end BlockReplayAt

end CompoundContinuation
end Cpp
