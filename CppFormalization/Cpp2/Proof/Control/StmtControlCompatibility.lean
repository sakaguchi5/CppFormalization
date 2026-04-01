import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

/-!
# Proof.Control.StmtControlCompatibility

`HasTypeStmtCI` は multi-exit relation なので、
abrupt control では同じ statement に複数の post-environment が立ちうる。
そのため preservation は、単に
`HasTypeStmtCI k Γ s Δ` と `BigStepStmt σ s ctrl σ'`
を並べるだけでは足りず、
「この typing 導出がこの実行導出に対応している」ことを別に持つ必要がある。

`StmtControlCompatible` / `BlockControlCompatible`
がその proof-relevant matching である。
-/

mutual

inductive StmtControlCompatible :
    {k : ControlKind} → {Γ Δ : TypeEnv} → {s : CppStmt} →
    {σ : State} → {ctrl : CtrlResult} → {σ' : State} →
    HasTypeStmtCI k Γ s Δ → BigStepStmt σ s ctrl σ' → Prop where
  | skip
      {Γ : TypeEnv} {σ : State} :
      StmtControlCompatible HasTypeStmtCI.skip BigStepStmt.skip

  | exprStmt
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
      {hv : HasValueType Γ e τ} {hstep : BigStepStmt σ (.exprStmt e) .normal σ} :
      StmtControlCompatible (HasTypeStmtCI.exprStmt hv) hstep

  | assign
      {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {e : ValExpr} {τ : CppType}
      {hp : HasPlaceType Γ p τ} {hv : HasValueType Γ e τ}
      {hstep : BigStepStmt σ (.assign p e) .normal σ'} :
      StmtControlCompatible (HasTypeStmtCI.assign hp hv) hstep

  | declareObjNone
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
      {hfresh : currentTypeScopeFresh Γ x} {hobj : ObjectType τ}
      {hstep : BigStepStmt σ (.declareObj τ x none) .normal σ'} :
      StmtControlCompatible (HasTypeStmtCI.declareObjNone hfresh hobj) hstep

  | declareObjSome
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {e : ValExpr}
      {hfresh : currentTypeScopeFresh Γ x} {hobj : ObjectType τ}
      {hv : HasValueType Γ e τ}
      {hstep : BigStepStmt σ (.declareObj τ x (some e)) .normal σ'} :
      StmtControlCompatible (HasTypeStmtCI.declareObjSome hfresh hobj hv) hstep

  | declareRef
      {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p : PlaceExpr}
      {hfresh : currentTypeScopeFresh Γ x} {hp : HasPlaceType Γ p τ}
      {hstep : BigStepStmt σ (.declareRef τ x p) .normal σ'} :
      StmtControlCompatible (HasTypeStmtCI.declareRef hfresh hp) hstep

  | breakStmt
      {Γ : TypeEnv} {σ : State} :
      StmtControlCompatible HasTypeStmtCI.breakStmt BigStepStmt.breakStmt

  | continueStmt
      {Γ : TypeEnv} {σ : State} :
      StmtControlCompatible HasTypeStmtCI.continueStmt BigStepStmt.continueStmt

  | returnNone
      {Γ : TypeEnv} {σ : State} :
      StmtControlCompatible HasTypeStmtCI.returnNone BigStepStmt.returnNoneStmt

  | returnSome
      {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {rv : Value}
      {hv : HasValueType Γ e τ}
      {hstep : BigStepStmt σ (.returnStmt (some e)) (.returnResult (some rv)) σ} :
      StmtControlCompatible (HasTypeStmtCI.returnSome hv) hstep

  | seq_normal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ σ₂ : State} {ctrl : CtrlResult}
      {htyS : HasTypeStmtCI .normalK Γ s Θ}
      {htyT : HasTypeStmtCI k Θ t Δ}
      {hstepS : BigStepStmt σ s .normal σ₁}
      {hstepT : BigStepStmt σ₁ t ctrl σ₂} :
      StmtControlCompatible htyS hstepS →
      StmtControlCompatible htyT hstepT →
      StmtControlCompatible (HasTypeStmtCI.seq_normal htyS htyT)
        (BigStepStmt.seqNormal hstepS hstepT)

  | seq_break
      {Γ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .breakK Γ s Δ}
      {hstepS : BigStepStmt σ s .breakResult σ₁} :
      StmtControlCompatible htyS hstepS →
      StmtControlCompatible (HasTypeStmtCI.seq_break htyS)
        (BigStepStmt.seqBreak hstepS)

  | seq_continue
      {Γ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .continueK Γ s Δ}
      {hstepS : BigStepStmt σ s .continueResult σ₁} :
      StmtControlCompatible htyS hstepS →
      StmtControlCompatible (HasTypeStmtCI.seq_continue htyS)
        (BigStepStmt.seqContinue hstepS)

  | seq_return
      {Γ Δ : TypeEnv} {s t : CppStmt}
      {σ σ₁ : State} {rv : Option Value}
      {htyS : HasTypeStmtCI .returnK Γ s Δ}
      {hstepS : BigStepStmt σ s (.returnResult rv) σ₁} :
      StmtControlCompatible htyS hstepS →
      StmtControlCompatible (HasTypeStmtCI.seq_return htyS)
        (BigStepStmt.seqReturn hstepS)

  | ite_true
      {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt}
      {σ σ' : State} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {htyS : HasTypeStmtCI k Γ s Δ}
      {htyT : HasTypeStmtCI k Γ t Δ}
      {hcond : BigStepValue σ c (.bool true)}
      {hstepS : BigStepStmt σ s ctrl σ'} :
      StmtControlCompatible htyS hstepS →
      StmtControlCompatible (HasTypeStmtCI.ite hc htyS htyT)
        (BigStepStmt.iteTrue hcond hstepS)

  | ite_false
      {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt}
      {σ σ' : State} {ctrl : CtrlResult}
      {hc : HasValueType Γ c (.base .bool)}
      {htyS : HasTypeStmtCI k Γ s Δ}
      {htyT : HasTypeStmtCI k Γ t Δ}
      {hcond : BigStepValue σ c (.bool false)}
      {hstepT : BigStepStmt σ t ctrl σ'} :
      StmtControlCompatible htyT hstepT →
      StmtControlCompatible (HasTypeStmtCI.ite hc htyS htyT)
        (BigStepStmt.iteFalse hcond hstepT)

  | while_false_normal
      {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hcond : BigStepValue σ c (.bool false)} :
      StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC)
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
      StmtControlCompatible hN hbody →
      StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC) htail →
      StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC)
        (BigStepStmt.whileTrueNormal hcond hbody htail)

  | while_true_break
      {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
      {hc : HasValueType Γ c (.base .bool)}
      {hN : HasTypeStmtCI .normalK Γ body Γ}
      {hB : HasTypeStmtCI .breakK Γ body Γ}
      {hC : HasTypeStmtCI .continueK Γ body Γ}
      {hcond : BigStepValue σ c (.bool true)}
      {hbody : BigStepStmt σ body .breakResult σ₁} :
      StmtControlCompatible hB hbody →
      StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC)
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
      StmtControlCompatible hC hbody →
      StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC) htail →
      StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC)
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
      StmtControlCompatible hN hbody →
      StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR) htail →
      StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR)
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
      StmtControlCompatible hC hbody →
      StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR) htail →
      StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR)
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
      StmtControlCompatible hR hbody →
      StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR)
        (BigStepStmt.whileTrueReturn hcond hbody)

    | block
      {k : ControlKind} {Γ Θ : TypeEnv} {ss : StmtBlock}
      {σ σ₀ σ₁ σ₂ : State} {ctrl : CtrlResult}
      {htyB : HasTypeBlockCI k (pushTypeScope Γ) ss Θ}
      {hopen : OpenScope σ σ₀}
      {hbody : BigStepBlock σ₀ ss ctrl σ₁}
      {hclose : CloseScope σ₁ σ₂} :
      BlockControlCompatible htyB hbody →
      StmtControlCompatible (HasTypeStmtCI.block htyB)
        (BigStepStmt.block hopen hbody hclose)

inductive BlockControlCompatible :
    {k : ControlKind} → {Γ Δ : TypeEnv} → {ss : StmtBlock} →
    {σ : State} → {ctrl : CtrlResult} → {σ' : State} →
    HasTypeBlockCI k Γ ss Δ → BigStepBlock σ ss ctrl σ' → Prop where
  | nil
      {Γ : TypeEnv} {σ : State} :
      BlockControlCompatible HasTypeBlockCI.nil BigStepBlock.nil

  | cons_normal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ σ₂ : State} {ctrl : CtrlResult}
      {htyS : HasTypeStmtCI .normalK Γ s Θ}
      {htyT : HasTypeBlockCI k Θ ss Δ}
      {hstepS : BigStepStmt σ s .normal σ₁}
      {hstepT : BigStepBlock σ₁ ss ctrl σ₂} :
      StmtControlCompatible htyS hstepS →
      BlockControlCompatible htyT hstepT →
      BlockControlCompatible (HasTypeBlockCI.cons_normal htyS htyT)
        (BigStepBlock.consNormal hstepS hstepT)

  | cons_break
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .breakK Γ s Δ}
      {hstepS : BigStepStmt σ s .breakResult σ₁} :
      StmtControlCompatible htyS hstepS →
      BlockControlCompatible (HasTypeBlockCI.cons_break htyS)
        (BigStepBlock.consBreak hstepS)

  | cons_continue
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ : State}
      {htyS : HasTypeStmtCI .continueK Γ s Δ}
      {hstepS : BigStepStmt σ s .continueResult σ₁} :
      StmtControlCompatible htyS hstepS →
      BlockControlCompatible (HasTypeBlockCI.cons_continue htyS)
        (BigStepBlock.consContinue hstepS)

  | cons_return
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
      {σ σ₁ : State} {rv : Option Value}
      {htyS : HasTypeStmtCI .returnK Γ s Δ}
      {hstepS : BigStepStmt σ s (.returnResult rv) σ₁} :
      StmtControlCompatible htyS hstepS →
      BlockControlCompatible (HasTypeBlockCI.cons_return htyS)
        (BigStepBlock.consReturn hstepS)

end

end Cpp
