--import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
--import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ConditionalNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.WhileNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Closure.Transitions.Minor.OpenScopeDecomposition

namespace Cpp

/-!
# Proof.Preservation.StmtControlKernel

`StmtControlCompatible` / `BlockControlCompatible` に対する preservation kernel.

方針:
- `mutual theorem` で直接定義するのではなく、compatibility recursor を使う。
- ただし statement と block の相互性そのものは残るので、
  motive は 2 本 (`StmtCompatGoal` / `BlockCompatGoal`) を同時に与える。
- while の difficult branch は
  `WhileCompatCtx` と 2 本の helper theorem に押し込める。
-/


/-- while compatibility branch が必要とする局所文脈。 -/
private structure WhileCompatCtx
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  condReady : ExprReadyConcrete Γ σ c (.base .bool)
  bodyBoundary : LoopBodyBoundaryCI Γ σ body
  reentry : LoopReentryKernelCI Γ c body

mutual

/-- compatibility 導出木に沿って運ぶ statement-side の Prop-level context. -/
private inductive StmtCompatCtx :
    {k : ControlKind} → {Γ Δ : TypeEnv} → {s : CppStmt} →
    {σ : State} → {ctrl : CtrlResult} → {σ' : State} →
    HasTypeStmtCI k Γ s Δ → BigStepStmt σ s ctrl σ' → Prop
  | skip
      {Γ : TypeEnv} {σ : State} :
      StmtCompatCtx HasTypeStmtCI.skip BigStepStmt.skip

  | exprStmt
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
      {hv : HasValueType Γ e τ}
      {hstep : BigStepStmt σ (.exprStmt e) .normal σ} :
      StmtCompatCtx (HasTypeStmtCI.exprStmt hv) hstep

  | assign
      {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {e : ValExpr} {τ : CppType}
      {hp : HasPlaceType Γ p τ} {hv : HasValueType Γ e τ}
      {hstep : BigStepStmt σ (.assign p e) .normal σ'} :
      StmtCompatCtx (HasTypeStmtCI.assign hp hv) hstep

  | declareObjNone
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
      {hfresh : currentTypeScopeFresh Γ x} {hobj : ObjectType τ}
      {hstep : BigStepStmt σ (.declareObj τ x none) .normal σ'} :
      StmtCompatCtx (HasTypeStmtCI.declareObjNone hfresh hobj) hstep

  | declareObjSome
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {e : ValExpr}
      {hfresh : currentTypeScopeFresh Γ x} {hobj : ObjectType τ}
      {hv : HasValueType Γ e τ}
      {hstep : BigStepStmt σ (.declareObj τ x (some e)) .normal σ'} :
      StmtCompatCtx (HasTypeStmtCI.declareObjSome hfresh hobj hv) hstep

  | declareRef
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p : PlaceExpr}
      {hfresh : currentTypeScopeFresh Γ x} {hp : HasPlaceType Γ p τ}
      {hstep : BigStepStmt σ (.declareRef τ x p) .normal σ'} :
      StmtCompatCtx (HasTypeStmtCI.declareRef hfresh hp) hstep

  | breakStmt
      {Γ : TypeEnv} {σ : State} :
      StmtCompatCtx HasTypeStmtCI.breakStmt BigStepStmt.breakStmt

  | continueStmt
      {Γ : TypeEnv} {σ : State} :
      StmtCompatCtx HasTypeStmtCI.continueStmt BigStepStmt.continueStmt

  | returnNone
      {Γ : TypeEnv} {σ : State} :
      StmtCompatCtx HasTypeStmtCI.returnNone BigStepStmt.returnNoneStmt

  | returnSome
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {rv : Value}
      {hv : HasValueType Γ e τ}
      {hstep : BigStepStmt σ (.returnStmt (some e)) (.returnResult (some rv)) σ} :
      StmtCompatCtx (HasTypeStmtCI.returnSome hv) hstep

  | seq_normal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ σ₂ : State} {ctrl : CtrlResult}
      {htyS : HasTypeStmtCI .normalK Γ s Θ}
      {htyT : HasTypeStmtCI k Θ t Δ}
      {hstepS : BigStepStmt σ s .normal σ₁}
      {hstepT : BigStepStmt σ₁ t ctrl σ₂} :
      StmtCompatCtx htyS hstepS →
      StmtCompatCtx htyT hstepT →
      StmtCompatCtx (HasTypeStmtCI.seq_normal htyS htyT)
        (BigStepStmt.seqNormal hstepS hstepT)

  | seq_break
      {Γ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .breakK Γ s Δ}
      {hstepS : BigStepStmt σ s .breakResult σ₁} :
      StmtCompatCtx htyS hstepS →
      StmtCompatCtx (HasTypeStmtCI.seq_break htyS)
        (BigStepStmt.seqBreak hstepS)

  | seq_continue
      {Γ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .continueK Γ s Δ}
      {hstepS : BigStepStmt σ s .continueResult σ₁} :
      StmtCompatCtx htyS hstepS →
      StmtCompatCtx (HasTypeStmtCI.seq_continue htyS)
        (BigStepStmt.seqContinue hstepS)

  | seq_return
      {Γ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ : State} {rv : Option Value}
      {htyS : HasTypeStmtCI .returnK Γ s Δ}
      {hstepS : BigStepStmt σ s (.returnResult rv) σ₁} :
      StmtCompatCtx htyS hstepS →
      StmtCompatCtx (HasTypeStmtCI.seq_return htyS)
        (BigStepStmt.seqReturn hstepS)

  | ite_true
      {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt}
      {σ σ' : State} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {htyS : HasTypeStmtCI k Γ s Δ}
      {htyT : HasTypeStmtCI k Γ t Δ}
      {hcond : BigStepValue σ c (.bool true)}
      {hstepS : BigStepStmt σ s ctrl σ'} :
      StmtCompatCtx htyS hstepS →
      StmtCompatCtx (HasTypeStmtCI.ite hc htyS htyT)
        (BigStepStmt.iteTrue hcond hstepS)

  | ite_false
      {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt}
      {σ σ' : State} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {htyS : HasTypeStmtCI k Γ s Δ}
      {htyT : HasTypeStmtCI k Γ t Δ}
      {hcond : BigStepValue σ c (.bool false)}
      {hstepT : BigStepStmt σ t ctrl σ'} :
      StmtCompatCtx htyT hstepT →
      StmtCompatCtx (HasTypeStmtCI.ite hc htyS htyT)
        (BigStepStmt.iteFalse hcond hstepT)

  | while_false_normal
      {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hcond : BigStepValue σ c (.bool false)} :
      StmtCompatCtx (HasTypeStmtCI.while_normal hc hN hB hC)
        (BigStepStmt.whileFalse hcond)

  | while_true_normal_normal
      {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hcond : BigStepValue σ c (.bool true)}
      {hbody : BigStepStmt σ body .normal σ₁}
      {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂} :
      WhileCompatCtx Γ σ c body →
      StmtCompatCtx hN hbody →
      StmtCompatCtx (HasTypeStmtCI.while_normal hc hN hB hC) htail →
      StmtCompatCtx (HasTypeStmtCI.while_normal hc hN hB hC)
        (BigStepStmt.whileTrueNormal hcond hbody htail)

  | while_true_break
      {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hcond : BigStepValue σ c (.bool true)}
      {hbody : BigStepStmt σ body .breakResult σ₁} :
      StmtCompatCtx hB hbody →
      StmtCompatCtx (HasTypeStmtCI.while_normal hc hN hB hC)
        (BigStepStmt.whileTrueBreak hcond hbody)

  | while_true_continue_normal
      {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hcond : BigStepValue σ c (.bool true)}
      {hbody : BigStepStmt σ body .continueResult σ₁}
      {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂} :
      WhileCompatCtx Γ σ c body →
      StmtCompatCtx hC hbody →
      StmtCompatCtx (HasTypeStmtCI.while_normal hc hN hB hC) htail →
      StmtCompatCtx (HasTypeStmtCI.while_normal hc hN hB hC)
        (BigStepStmt.whileTrueContinue hcond hbody htail)

  | while_true_normal_return
      {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hR : HasTypeStmtCI .returnK Γ body Δ}
      {hcond : BigStepValue σ c (.bool true)}
      {rv : Option Value}
      {hbody : BigStepStmt σ body .normal σ₁}
      {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂} :
      WhileCompatCtx Γ σ c body →
      StmtCompatCtx hN hbody →
      StmtCompatCtx (HasTypeStmtCI.while_return hc hN hB hC hR) htail →
      StmtCompatCtx (HasTypeStmtCI.while_return hc hN hB hC hR)
        (BigStepStmt.whileTrueNormal hcond hbody htail)

  | while_true_continue_return
      {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hR : HasTypeStmtCI .returnK Γ body Δ}
      {hcond : BigStepValue σ c (.bool true)}
      {rv : Option Value}
      {hbody : BigStepStmt σ body .continueResult σ₁}
      {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂} :
      WhileCompatCtx Γ σ c body →
      StmtCompatCtx hC hbody →
      StmtCompatCtx (HasTypeStmtCI.while_return hc hN hB hC hR) htail →
      StmtCompatCtx (HasTypeStmtCI.while_return hc hN hB hC hR)
        (BigStepStmt.whileTrueContinue hcond hbody htail)

  | while_true_return
      {Γ Δ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt} {rv : Option Value}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hR : HasTypeStmtCI .returnK Γ body Δ}
      {hcond : BigStepValue σ c (.bool true)}
      {hbody : BigStepStmt σ body (.returnResult rv) σ₁} :
      StmtCompatCtx hR hbody →
      StmtCompatCtx (HasTypeStmtCI.while_return hc hN hB hC hR)
        (BigStepStmt.whileTrueReturn hcond hbody)

  | block
      {k : ControlKind} {Γ Θ : TypeEnv} {ss : StmtBlock}
      {σ σ₀ σ₁ σ₂ : State} {ctrl : CtrlResult}
      {htyB : HasTypeBlockCI k (pushTypeScope Γ) ss Θ}
      {hopen : OpenScope σ σ₀}
      {hbody : BigStepBlock σ₀ ss ctrl σ₁}
      {hclose : CloseScope σ₁ σ₂} :
      BlockCompatCtx htyB hbody →
      StmtCompatCtx (HasTypeStmtCI.block htyB)
        (BigStepStmt.block hopen hbody hclose)

/-- compatibility 導出木に沿って運ぶ block-side の Prop-level context. -/
private inductive BlockCompatCtx :
    {k : ControlKind} → {Γ Δ : TypeEnv} → {ss : StmtBlock} →
    {σ : State} → {ctrl : CtrlResult} → {σ' : State} →
    HasTypeBlockCI k Γ ss Δ → BigStepBlock σ ss ctrl σ' → Prop
  | nil
      {Γ : TypeEnv} {σ : State} :
      BlockCompatCtx HasTypeBlockCI.nil BigStepBlock.nil

  | cons_normal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ σ₂ : State} {ctrl : CtrlResult}
      {htyS : HasTypeStmtCI .normalK Γ s Θ}
      {htyT : HasTypeBlockCI k Θ ss Δ}
      {hstepS : BigStepStmt σ s .normal σ₁}
      {hstepT : BigStepBlock σ₁ ss ctrl σ₂} :
      StmtCompatCtx htyS hstepS →
      BlockCompatCtx htyT hstepT →
      BlockCompatCtx (HasTypeBlockCI.cons_normal htyS htyT)
        (BigStepBlock.consNormal hstepS hstepT)

  | cons_break
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .breakK Γ s Δ}
      {hstepS : BigStepStmt σ s .breakResult σ₁} :
      StmtCompatCtx htyS hstepS →
      BlockCompatCtx (HasTypeBlockCI.cons_break htyS)
        (BigStepBlock.consBreak hstepS)

  | cons_continue
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .continueK Γ s Δ}
      {hstepS : BigStepStmt σ s .continueResult σ₁} :
      StmtCompatCtx htyS hstepS →
      BlockCompatCtx (HasTypeBlockCI.cons_continue htyS)
        (BigStepBlock.consContinue hstepS)

  | cons_return
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ : State} {rv : Option Value}
      {htyS : HasTypeStmtCI .returnK Γ s Δ}
      {hstepS : BigStepStmt σ s (.returnResult rv) σ₁} :
      StmtCompatCtx htyS hstepS →
      BlockCompatCtx (HasTypeBlockCI.cons_return htyS)
        (BigStepBlock.consReturn hstepS)

end


end Cpp
