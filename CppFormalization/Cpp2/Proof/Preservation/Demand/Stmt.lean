import CppFormalization.Cpp2.Proof.Preservation.Demand.Expr
import CppFormalization.Cpp2.Typing.ControlIndexed

namespace Cpp

/-!
# Proof.Preservation.Demand.Stmt

Path-sensitive execution demand for statements and blocks.

The important design point is the `seqNormal` / `consNormal` shape:

* the head statement has a demand at the pre-state;
* the tail statement/block has a demand at the post-state produced by the head.

So this file does not assert that readiness is transported through a normal step.
It records the readiness demanded at the point where execution actually reaches
that subprogram.
-/

mutual

/--
Demand evidence consumed by preservation along one concrete statement execution.

`StmtExecutionDemand Γ σ st ctrl σ' Δ` means: along this concrete execution of
`st` from `(Γ, σ)` to `(Δ, σ')`, every expression/place/statement actually
executed has its readiness demanded at the state where it is executed.
-/
inductive StmtExecutionDemand :
    TypeEnv → State → CppStmt → CtrlResult → State → TypeEnv → Prop where

  | skip {Γ : TypeEnv} {σ : State} :
      StmtExecutionDemand Γ σ .skip .normal σ Γ

  | exprStmt
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {v : Value} :
      HasValueType Γ e τ →
      ExprExecutionDemand Γ σ e τ →
      BigStepValue σ e v →
      StmtExecutionDemand Γ σ (.exprStmt e) .normal σ Γ

  | assign
      {Γ : TypeEnv} {σ σ' : State}
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} {v : Value} :
      HasPlaceType Γ p τ →
      PlaceExecutionDemand Γ σ p τ →
      HasValueType Γ e τ →
      ExprExecutionDemand Γ σ e τ →
      BigStepValue σ e v →
      Assigns σ p v σ' →
      StmtExecutionDemand Γ σ (.assign p e) .normal σ' Γ

  | declareObjNone
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      DeclaresObject σ τ x none σ' →
      StmtExecutionDemand Γ σ (.declareObj τ x none) .normal σ'
        (declareTypeObject Γ x τ)

  | declareObjSome
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
      {e : ValExpr} {v : Value} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      HasValueType Γ e τ →
      ExprExecutionDemand Γ σ e τ →
      BigStepValue σ e v →
      DeclaresObject σ τ x (some v) σ' →
      StmtExecutionDemand Γ σ (.declareObj τ x (some e)) .normal σ'
        (declareTypeObject Γ x τ)

  | declareRef
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
      {p : PlaceExpr} {a : Nat} :
      currentTypeScopeFresh Γ x →
      HasPlaceType Γ p τ →
      PlaceExecutionDemand Γ σ p τ →
      BigStepPlace σ p a →
      DeclaresRef σ τ x a σ' →
      StmtExecutionDemand Γ σ (.declareRef τ x p) .normal σ'
        (declareTypeRef Γ x τ)

  | breakStmt {Γ : TypeEnv} {σ : State} :
      StmtExecutionDemand Γ σ .breakStmt .breakResult σ Γ

  | continueStmt {Γ : TypeEnv} {σ : State} :
      StmtExecutionDemand Γ σ .continueStmt .continueResult σ Γ

  | returnNone {Γ : TypeEnv} {σ : State} :
      StmtExecutionDemand Γ σ (.returnStmt none) (.returnResult none) σ Γ

  | returnSome
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {v : Value} :
      HasValueType Γ e τ →
      ExprExecutionDemand Γ σ e τ →
      BigStepValue σ e v →
      StmtExecutionDemand Γ σ (.returnStmt (some e)) (.returnResult (some v)) σ Γ

  | seqNormal
      {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {s t : CppStmt} {ctrl : CtrlResult} :
      StmtExecutionDemand Γ σ s .normal σ₁ Θ →
      StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ →
      StmtExecutionDemand Γ σ (.seq s t) ctrl σ₂ Δ

  | seqBreak
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s t : CppStmt} :
      StmtExecutionDemand Γ σ s .breakResult σ₁ Δ →
      StmtExecutionDemand Γ σ (.seq s t) .breakResult σ₁ Δ

  | seqContinue
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s t : CppStmt} :
      StmtExecutionDemand Γ σ s .continueResult σ₁ Δ →
      StmtExecutionDemand Γ σ (.seq s t) .continueResult σ₁ Δ

  | seqReturn
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s t : CppStmt} {rv : Option Value} :
      StmtExecutionDemand Γ σ s (.returnResult rv) σ₁ Δ →
      StmtExecutionDemand Γ σ (.seq s t) (.returnResult rv) σ₁ Δ

  | iteTrue
      {Γ Δ : TypeEnv} {σ σ' : State}
      {c : ValExpr} {s t : CppStmt} {ctrl : CtrlResult} :
      HasValueType Γ c (.base .bool) →
      ExprExecutionDemand Γ σ c (.base .bool) →
      BigStepValue σ c (.bool true) →
      StmtExecutionDemand Γ σ s ctrl σ' Δ →
      StmtExecutionDemand Γ σ (.ite c s t) ctrl σ' Δ

  | iteFalse
      {Γ Δ : TypeEnv} {σ σ' : State}
      {c : ValExpr} {s t : CppStmt} {ctrl : CtrlResult} :
      HasValueType Γ c (.base .bool) →
      ExprExecutionDemand Γ σ c (.base .bool) →
      BigStepValue σ c (.bool false) →
      StmtExecutionDemand Γ σ t ctrl σ' Δ →
      StmtExecutionDemand Γ σ (.ite c s t) ctrl σ' Δ

  | whileFalse
      {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
      HasValueType Γ c (.base .bool) →
      ExprExecutionDemand Γ σ c (.base .bool) →
      BigStepValue σ c (.bool false) →
      StmtExecutionDemand Γ σ (.whileStmt c body) .normal σ Γ

  | whileTrueNormal
      {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {c : ValExpr} {body : CppStmt} {ctrl : CtrlResult} :
      HasValueType Γ c (.base .bool) →
      ExprExecutionDemand Γ σ c (.base .bool) →
      BigStepValue σ c (.bool true) →
      StmtExecutionDemand Γ σ body .normal σ₁ Γ →
      StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ₂ Δ →
      StmtExecutionDemand Γ σ (.whileStmt c body) ctrl σ₂ Δ

  | whileTrueBreak
      {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt} :
      HasValueType Γ c (.base .bool) →
      ExprExecutionDemand Γ σ c (.base .bool) →
      BigStepValue σ c (.bool true) →
      StmtExecutionDemand Γ σ body .breakResult σ₁ Γ →
      StmtExecutionDemand Γ σ (.whileStmt c body) .normal σ₁ Γ

  | whileTrueContinue
      {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {c : ValExpr} {body : CppStmt} {ctrl : CtrlResult} :
      HasValueType Γ c (.base .bool) →
      ExprExecutionDemand Γ σ c (.base .bool) →
      BigStepValue σ c (.bool true) →
      StmtExecutionDemand Γ σ body .continueResult σ₁ Γ →
      StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ₂ Δ →
      StmtExecutionDemand Γ σ (.whileStmt c body) ctrl σ₂ Δ

  | whileTrueReturn
      {Γ Δ : TypeEnv} {σ σ₁ : State}
      {c : ValExpr} {body : CppStmt} {rv : Option Value} :
      HasValueType Γ c (.base .bool) →
      ExprExecutionDemand Γ σ c (.base .bool) →
      BigStepValue σ c (.bool true) →
      StmtExecutionDemand Γ σ body (.returnResult rv) σ₁ Δ →
      StmtExecutionDemand Γ σ (.whileStmt c body) (.returnResult rv) σ₁ Δ

  | block
      {Γ Θ : TypeEnv} {σ σ₀ σ₁ σ₂ : State}
      {ss : StmtBlock} {ctrl : CtrlResult} :
      OpenScope σ σ₀ →
      BlockExecutionDemand (pushTypeScope Γ) σ₀ ss ctrl σ₁ Θ →
      CloseScope σ₁ σ₂ →
      StmtExecutionDemand Γ σ (.block ss) ctrl σ₂ Γ

/--
Demand evidence consumed by preservation along one concrete block execution.
-/
inductive BlockExecutionDemand :
    TypeEnv → State → StmtBlock → CtrlResult → State → TypeEnv → Prop where

  | nil {Γ : TypeEnv} {σ : State} :
      BlockExecutionDemand Γ σ .nil .normal σ Γ

  | consNormal
      {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {s : CppStmt} {ss : StmtBlock} {ctrl : CtrlResult} :
      StmtExecutionDemand Γ σ s .normal σ₁ Θ →
      BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ →
      BlockExecutionDemand Γ σ (.cons s ss) ctrl σ₂ Δ

  | consBreak
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock} :
      StmtExecutionDemand Γ σ s .breakResult σ₁ Δ →
      BlockExecutionDemand Γ σ (.cons s ss) .breakResult σ₁ Δ

  | consContinue
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock} :
      StmtExecutionDemand Γ σ s .continueResult σ₁ Δ →
      BlockExecutionDemand Γ σ (.cons s ss) .continueResult σ₁ Δ

  | consReturn
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock}
      {rv : Option Value} :
      StmtExecutionDemand Γ σ s (.returnResult rv) σ₁ Δ →
      BlockExecutionDemand Γ σ (.cons s ss) (.returnResult rv) σ₁ Δ

end

end Cpp
