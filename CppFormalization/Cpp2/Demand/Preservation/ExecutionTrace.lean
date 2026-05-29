import CppFormalization.Cpp2.Demand.Preservation.Stmt

namespace Cpp

/-!
# Proof.Preservation.Demand.ExecutionTrace

Alignment between path-sensitive execution demand and concrete big-step
execution.

`StmtExecutionDemand` is intentionally path-sensitive, but the demand evidence
alone should not be allowed to choose a branch independently of the actual
`BigStepStmt` constructor.  These mutually inductive predicates say that demand
follows the same execution path as the concrete big-step derivation.
-/

mutual

/--
`StmtDemandFollowsStep demand step` means that the statement demand evidence
uses the same semantic branch structure as `step`.
-/
inductive StmtDemandFollowsStep :
    {Γ Δ : TypeEnv} → {st : CppStmt} →
    {σ : State} → {ctrl : CtrlResult} → {σ' : State} →
    StmtExecutionDemand Γ σ st ctrl σ' Δ →
    BigStepStmt σ st ctrl σ' → Prop where

  | skip {Γ : TypeEnv} {σ : State} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.skip (Γ := Γ) (σ := σ))
        (BigStepStmt.skip (σ := σ))

  | exprStmt
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {v : Value}
      {hty : HasValueType Γ e τ}
      {hready : ExprExecutionDemand Γ σ e τ}
      {hval : BigStepValue σ e v} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.exprStmt hty hready hval)
        (BigStepStmt.expr hval)

  | assign
      {Γ : TypeEnv} {σ σ' : State}
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} {v : Value}
      {hpty : HasPlaceType Γ p τ}
      {hpready : PlaceExecutionDemand Γ σ p τ}
      {hvty : HasValueType Γ e τ}
      {heready : ExprExecutionDemand Γ σ e τ}
      {hval : BigStepValue σ e v}
      {hassign : Assigns σ p v σ'} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.assign hpty hpready hvty heready hval hassign)
        (BigStepStmt.assign hval hassign)

  | declareObjNone
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
      {hfresh : currentTypeScopeFresh Γ x}
      {hobj : ObjectType τ}
      {hdecl : DeclaresObject σ τ x none σ'} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.declareObjNone hfresh hobj hdecl)
        (BigStepStmt.declareObjNone hdecl)

  | declareObjSome
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
      {e : ValExpr} {v : Value}
      {hfresh : currentTypeScopeFresh Γ x}
      {hobj : ObjectType τ}
      {hty : HasValueType Γ e τ}
      {hready : ExprExecutionDemand Γ σ e τ}
      {hval : BigStepValue σ e v}
      {hdecl : DeclaresObject σ τ x (some v) σ'} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.declareObjSome hfresh hobj hty hready hval hdecl)
        (BigStepStmt.declareObjSome hval hdecl)

  | declareRef
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
      {p : PlaceExpr} {a : Nat}
      {hfresh : currentTypeScopeFresh Γ x}
      {hpty : HasPlaceType Γ p τ}
      {hpready : PlaceExecutionDemand Γ σ p τ}
      {hplace : BigStepPlace σ p a}
      {hdecl : DeclaresRef σ τ x a σ'} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.declareRef hfresh hpty hpready hplace hdecl)
        (BigStepStmt.declareRef hplace hdecl)

  | breakStmt {Γ : TypeEnv} {σ : State} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.breakStmt (Γ := Γ) (σ := σ))
        (BigStepStmt.breakStmt (σ := σ))

  | continueStmt {Γ : TypeEnv} {σ : State} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.continueStmt (Γ := Γ) (σ := σ))
        (BigStepStmt.continueStmt (σ := σ))

  | returnNone {Γ : TypeEnv} {σ : State} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.returnNone (Γ := Γ) (σ := σ))
        (BigStepStmt.returnNoneStmt (σ := σ))

  | returnSome
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {v : Value}
      {hty : HasValueType Γ e τ}
      {hready : ExprExecutionDemand Γ σ e τ}
      {hval : BigStepValue σ e v} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.returnSome hty hready hval)
        (BigStepStmt.returnSome hval)

  | seqNormal
      {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {s t : CppStmt} {ctrl : CtrlResult}
      {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
      {dTail : StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ}
      {stepHead : BigStepStmt σ s .normal σ₁}
      {stepTail : BigStepStmt σ₁ t ctrl σ₂} :
      StmtDemandFollowsStep dHead stepHead →
      StmtDemandFollowsStep dTail stepTail →
      StmtDemandFollowsStep
        (StmtExecutionDemand.seqNormal dHead dTail)
        (BigStepStmt.seqNormal stepHead stepTail)

  | seqBreak
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
      {dHead : StmtExecutionDemand Γ σ s .breakResult σ₁ Δ}
      {stepHead : BigStepStmt σ s .breakResult σ₁} :
      StmtDemandFollowsStep dHead stepHead →
      StmtDemandFollowsStep
        (StmtExecutionDemand.seqBreak (t := t) dHead)
        (BigStepStmt.seqBreak (t := t) stepHead)

  | seqContinue
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
      {dHead : StmtExecutionDemand Γ σ s .continueResult σ₁ Δ}
      {stepHead : BigStepStmt σ s .continueResult σ₁} :
      StmtDemandFollowsStep dHead stepHead →
      StmtDemandFollowsStep
        (StmtExecutionDemand.seqContinue (t := t) dHead)
        (BigStepStmt.seqContinue (t := t) stepHead)

  | seqReturn
      {Γ Δ : TypeEnv} {σ σ₁ : State} {s t : CppStmt} {rv : Option Value}
      {dHead : StmtExecutionDemand Γ σ s (.returnResult rv) σ₁ Δ}
      {stepHead : BigStepStmt σ s (.returnResult rv) σ₁} :
      StmtDemandFollowsStep dHead stepHead →
      StmtDemandFollowsStep
        (StmtExecutionDemand.seqReturn (t := t) dHead)
        (BigStepStmt.seqReturn (t := t) stepHead)

  | iteTrue
      {Γ Δ : TypeEnv} {σ σ' : State}
      {c : ValExpr} {s t : CppStmt} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {hready : ExprExecutionDemand Γ σ c (.base .bool)}
      {hcond : BigStepValue σ c (.bool true)}
      {dBranch : StmtExecutionDemand Γ σ s ctrl σ' Δ}
      {stepBranch : BigStepStmt σ s ctrl σ'} :
      StmtDemandFollowsStep dBranch stepBranch →
      StmtDemandFollowsStep
        (StmtExecutionDemand.iteTrue (t := t) hc hready hcond dBranch)
        (BigStepStmt.iteTrue (t := t) hcond stepBranch)

  | iteFalse
      {Γ Δ : TypeEnv} {σ σ' : State}
      {c : ValExpr} {s t : CppStmt} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {hready : ExprExecutionDemand Γ σ c (.base .bool)}
      {hcond : BigStepValue σ c (.bool false)}
      {dBranch : StmtExecutionDemand Γ σ t ctrl σ' Δ}
      {stepBranch : BigStepStmt σ t ctrl σ'} :
      StmtDemandFollowsStep dBranch stepBranch →
      StmtDemandFollowsStep
        (StmtExecutionDemand.iteFalse (s := s) hc hready hcond dBranch)
        (BigStepStmt.iteFalse (s := s) hcond stepBranch)

  | whileFalse
      {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hready : ExprExecutionDemand Γ σ c (.base .bool)}
      {hcond : BigStepValue σ c (.bool false)} :
      StmtDemandFollowsStep
        (StmtExecutionDemand.whileFalse (body := body) hc hready hcond)
        (BigStepStmt.whileFalse (body := body) hcond)

  | whileTrueNormal
      {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {c : ValExpr} {body : CppStmt} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {hready : ExprExecutionDemand Γ σ c (.base .bool)}
      {hcond : BigStepValue σ c (.bool true)}
      {dBody : StmtExecutionDemand Γ σ body .normal σ₁ Γ}
      {dTail : StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ₂ Δ}
      {stepBody : BigStepStmt σ body .normal σ₁}
      {stepTail : BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂} :
      StmtDemandFollowsStep dBody stepBody →
      StmtDemandFollowsStep dTail stepTail →
      StmtDemandFollowsStep
        (StmtExecutionDemand.whileTrueNormal hc hready hcond dBody dTail)
        (BigStepStmt.whileTrueNormal hcond stepBody stepTail)

  | whileTrueBreak
      {Γ : TypeEnv} {σ σ₁ : State}
      {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hready : ExprExecutionDemand Γ σ c (.base .bool)}
      {hcond : BigStepValue σ c (.bool true)}
      {dBody : StmtExecutionDemand Γ σ body .breakResult σ₁ Γ}
      {stepBody : BigStepStmt σ body .breakResult σ₁} :
      StmtDemandFollowsStep dBody stepBody →
      StmtDemandFollowsStep
        (StmtExecutionDemand.whileTrueBreak hc hready hcond dBody)
        (BigStepStmt.whileTrueBreak hcond stepBody)

  | whileTrueContinue
      {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {c : ValExpr} {body : CppStmt} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {hready : ExprExecutionDemand Γ σ c (.base .bool)}
      {hcond : BigStepValue σ c (.bool true)}
      {dBody : StmtExecutionDemand Γ σ body .continueResult σ₁ Γ}
      {dTail : StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ₂ Δ}
      {stepBody : BigStepStmt σ body .continueResult σ₁}
      {stepTail : BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂} :
      StmtDemandFollowsStep dBody stepBody →
      StmtDemandFollowsStep dTail stepTail →
      StmtDemandFollowsStep
        (StmtExecutionDemand.whileTrueContinue hc hready hcond dBody dTail)
        (BigStepStmt.whileTrueContinue hcond stepBody stepTail)

  | whileTrueReturn
      {Γ Δ : TypeEnv} {σ σ₁ : State}
      {c : ValExpr} {body : CppStmt} {rv : Option Value}
      {hc : HasValueType Γ c (.base .bool)}
      {hready : ExprExecutionDemand Γ σ c (.base .bool)}
      {hcond : BigStepValue σ c (.bool true)}
      {dBody : StmtExecutionDemand Γ σ body (.returnResult rv) σ₁ Δ}
      {stepBody : BigStepStmt σ body (.returnResult rv) σ₁} :
      StmtDemandFollowsStep dBody stepBody →
      StmtDemandFollowsStep
        (StmtExecutionDemand.whileTrueReturn hc hready hcond dBody)
        (BigStepStmt.whileTrueReturn hcond stepBody)

  | block
      {Γ Θ : TypeEnv} {σ σ₀ σ₁ σ₂ : State}
      {ss : StmtBlock} {ctrl : CtrlResult}
      {hopen : OpenScope σ σ₀}
      {hExt : TopFrameExtensionOf Γ Θ}
      {dBody : BlockExecutionDemand (pushTypeScope Γ) σ₀ ss ctrl σ₁ Θ}
      {stepBody : BigStepBlock σ₀ ss ctrl σ₁}
      {hclose : CloseScope σ₁ σ₂} :
      BlockDemandFollowsStep dBody stepBody →
      StmtDemandFollowsStep
        (StmtExecutionDemand.block hopen hExt dBody hclose)
        (BigStepStmt.block hopen stepBody hclose)

/--
Block-demand analogue of `StmtDemandFollowsStep`.
-/
inductive BlockDemandFollowsStep :
    {Γ Δ : TypeEnv} → {ss : StmtBlock} →
    {σ : State} → {ctrl : CtrlResult} → {σ' : State} →
    BlockExecutionDemand Γ σ ss ctrl σ' Δ →
    BigStepBlock σ ss ctrl σ' → Prop where

  | nil {Γ : TypeEnv} {σ : State} :
      BlockDemandFollowsStep
        (BlockExecutionDemand.nil (Γ := Γ) (σ := σ))
        (BigStepBlock.nil (σ := σ))

  | consNormal
      {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
      {s : CppStmt} {ss : StmtBlock} {ctrl : CtrlResult}
      {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
      {dTail : BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ}
      {stepHead : BigStepStmt σ s .normal σ₁}
      {stepTail : BigStepBlock σ₁ ss ctrl σ₂} :
      StmtDemandFollowsStep dHead stepHead →
      BlockDemandFollowsStep dTail stepTail →
      BlockDemandFollowsStep
        (BlockExecutionDemand.consNormal dHead dTail)
        (BigStepBlock.consNormal stepHead stepTail)

  | consBreak
      {Γ Δ : TypeEnv} {σ σ₁ : State}
      {s : CppStmt} {ss : StmtBlock}
      {dHead : StmtExecutionDemand Γ σ s .breakResult σ₁ Δ}
      {stepHead : BigStepStmt σ s .breakResult σ₁} :
      StmtDemandFollowsStep dHead stepHead →
      BlockDemandFollowsStep
        (BlockExecutionDemand.consBreak (ss := ss) dHead)
        (BigStepBlock.consBreak (ss := ss) stepHead)

  | consContinue
      {Γ Δ : TypeEnv} {σ σ₁ : State}
      {s : CppStmt} {ss : StmtBlock}
      {dHead : StmtExecutionDemand Γ σ s .continueResult σ₁ Δ}
      {stepHead : BigStepStmt σ s .continueResult σ₁} :
      StmtDemandFollowsStep dHead stepHead →
      BlockDemandFollowsStep
        (BlockExecutionDemand.consContinue (ss := ss) dHead)
        (BigStepBlock.consContinue (ss := ss) stepHead)

  | consReturn
      {Γ Δ : TypeEnv} {σ σ₁ : State}
      {s : CppStmt} {ss : StmtBlock} {rv : Option Value}
      {dHead : StmtExecutionDemand Γ σ s (.returnResult rv) σ₁ Δ}
      {stepHead : BigStepStmt σ s (.returnResult rv) σ₁} :
      StmtDemandFollowsStep dHead stepHead →
      BlockDemandFollowsStep
        (BlockExecutionDemand.consReturn (ss := ss) dHead)
        (BigStepBlock.consReturn (ss := ss) stepHead)

end

end Cpp
