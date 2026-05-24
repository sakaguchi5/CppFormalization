import CppFormalization.Cpp2.Proof.Preservation.PrimitiveStmtNormalStateOnly
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernelSupport
import CppFormalization.Cpp2.Proof.Preservation.Scope.OpenPreservation
import CppFormalization.Cpp2.Proof.Preservation.Scope.ClosePreservation


set_option maxHeartbeats 0

namespace Cpp

/-!
# Proof.Preservation.StmtControlStateOnly

Ready-free / state-only preservation for control-compatible executions.

This file deliberately uses `StmtControlCompatible.rec` /
`BlockControlCompatible.rec` directly.

No `StmtReadyConcrete` / `BlockReadyConcrete` reconstruction appears here.
The theorem only says:

If a typing derivation and an execution derivation are compatible, then
`ScopedTypedStateConcrete` is preserved from the pre-state/type-env to the
post-state/type-env.
-/

/--
Statement control-compatible execution preserves scoped/typed state,
without requiring statement readiness.
-/
theorem stmt_control_preserves_scoped_typed_state_of_compatible_noReady
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  exact
    StmtControlCompatible.rec
      (motive_1 :=
        fun {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
            {σ : State} {ctrl : CtrlResult} {σ' : State}
            (hty : HasTypeStmtCI k Γ s Δ)
            (hstep : BigStepStmt σ s ctrl σ')
            (_hcomp : StmtControlCompatible hty hstep) =>
          ScopedTypedStateConcrete Γ σ →
          ScopedTypedStateConcrete Δ σ')
      (motive_2 :=
        fun {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
            {σ : State} {ctrl : CtrlResult} {σ' : State}
            (hty : HasTypeBlockCI k Γ ss Δ)
            (hstep : BigStepBlock σ ss ctrl σ')
            (_hcomp : BlockControlCompatible hty hstep) =>
          ScopedTypedStateConcrete Γ σ →
          ScopedTypedStateConcrete Δ σ')

      (skip :=
        fun {x : TypeEnv} {x_1 : State} {Γ₀ : TypeEnv} {σ₀ : State} =>
          fun hσ =>
            hσ)

      (exprStmt :=
        fun {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
            {hv : HasValueType Γ e τ}
            {hstep : BigStepStmt σ (.exprStmt e) .normal σ} =>
          fun hσ =>
            hσ)

      (assign :=
        fun {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {e : ValExpr}
            {τ : CppType}
            {hp : HasPlaceType Γ p τ}
            {hv : HasValueType Γ e τ}
            {hstep : BigStepStmt σ (.assign p e) .normal σ'} =>
          fun hσ =>
            assign_stmt_normal_preserves_scoped_typed_state_concrete_noReady
              (HasTypeStmtCI.assign hp hv)
              hσ
              hstep)

      (declareObjNone :=
        fun {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
            {hfresh : currentTypeScopeFresh Γ x}
            {hobj : ObjectType τ}
            {hstep : BigStepStmt σ (.declareObj τ x none) .normal σ'} =>
          fun hσ =>
            declareObj_stmt_normal_preserves_scoped_typed_state_concrete_noReady
              (HasTypeStmtCI.declareObjNone hfresh hobj)
              hσ
              hstep)

      (declareObjSome :=
        fun {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
            {e : ValExpr}
            {hfresh : currentTypeScopeFresh Γ x}
            {hobj : ObjectType τ}
            {hv : HasValueType Γ e τ}
            {hstep : BigStepStmt σ (.declareObj τ x (some e)) .normal σ'} =>
          fun hσ =>
            declareObj_stmt_normal_preserves_scoped_typed_state_concrete_noReady
              (HasTypeStmtCI.declareObjSome hfresh hobj hv)
              hσ
              hstep)

      (declareRef :=
        fun {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident}
            {p : PlaceExpr}
            {hfresh : currentTypeScopeFresh Γ x}
            {hp : HasPlaceType Γ p τ}
            {hstep : BigStepStmt σ (.declareRef τ x p) .normal σ'} =>
          fun hσ =>
            declareRef_stmt_normal_preserves_scoped_typed_state_concrete_noReady
              (HasTypeStmtCI.declareRef hfresh hp)
              hσ
              hstep)

      (breakStmt :=
        fun {x : TypeEnv} {x_1 : State} {Γ₀ : TypeEnv} {σ₀ : State} =>
          fun hσ =>
            hσ)

      (continueStmt :=
        fun {x : TypeEnv} {x_1 : State} {Γ₀ : TypeEnv} {σ₀ : State} =>
          fun hσ =>
            hσ)

      (returnNone :=
        fun {x : TypeEnv} {x_1 : State} {Γ₀ : TypeEnv} {σ₀ : State} =>
          fun hσ =>
            hσ)

      (returnSome :=
        fun {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
            {rv : Value}
            {hv : HasValueType Γ e τ}
            {hstep :
              BigStepStmt σ (.returnStmt (some e)) (.returnResult (some rv)) σ} =>
          fun hσ =>
            hσ)

      (seq_normal :=
        fun {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt}
            {σ σ₁ σ₂ : State} {ctrl : CtrlResult}
            {htyS : HasTypeStmtCI .normalK Γ s Θ}
            {htyT : HasTypeStmtCI k Θ t Δ}
            {hstepS : BigStepStmt σ s .normal σ₁}
            {hstepT : BigStepStmt σ₁ t ctrl σ₂}
            (hcompS : StmtControlCompatible htyS hstepS)
            (hcompT : StmtControlCompatible htyT hstepT)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Θ σ₁)
            (ihT :
              ScopedTypedStateConcrete Θ σ₁ →
              ScopedTypedStateConcrete Δ σ₂) =>
          fun hσ =>
            ihT (ihS hσ))

      (seq_break :=
        fun {x : CppStmt} {Γ Δ : TypeEnv} {s t : CppStmt}
            {σ σ₁ : State}
            {htyS : HasTypeStmtCI .breakK Γ s Δ}
            {hstepS : BigStepStmt σ s .breakResult σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ₁) =>
          ihS)

      (seq_continue :=
        fun {x : CppStmt} {Γ Δ : TypeEnv} {s t : CppStmt}
            {σ σ₁ : State}
            {htyS : HasTypeStmtCI .continueK Γ s Δ}
            {hstepS : BigStepStmt σ s .continueResult σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ₁) =>
          ihS)

      (seq_return :=
        fun {x : CppStmt} {Γ Δ : TypeEnv} {s t : CppStmt}
            {σ σ₁ : State} {rv : Option Value}
            {htyS : HasTypeStmtCI .returnK Γ s Δ}
            {hstepS : BigStepStmt σ s (.returnResult rv) σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ₁) =>
          ihS)

      (ite_true :=
        fun {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr}
            {s t : CppStmt}
            {σ σ' : State} {ctrl : CtrlResult}
            {hc : HasValueType Γ c (.base .bool)}
            {htyS : HasTypeStmtCI k Γ s Δ}
            {htyT : HasTypeStmtCI k Γ t Δ}
            {hcond : BigStepValue σ c (.bool true)}
            {hstepS : BigStepStmt σ s ctrl σ'}
            (hcompS : StmtControlCompatible htyS hstepS)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ') =>
          ihS)

      (ite_false :=
        fun {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr}
            {s t : CppStmt}
            {σ σ' : State} {ctrl : CtrlResult}
            {hc : HasValueType Γ c (.base .bool)}
            {htyS : HasTypeStmtCI k Γ s Δ}
            {htyT : HasTypeStmtCI k Γ t Δ}
            {hcond : BigStepValue σ c (.bool false)}
            {hstepT : BigStepStmt σ t ctrl σ'}
            (hcompT : StmtControlCompatible htyT hstepT)
            (ihT :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ') =>
          ihT)

      (while_false_normal :=
        fun {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
            {hc : HasValueType Γ c (.base .bool)}
            {hN : HasTypeStmtCI .normalK Γ body Γ}
            {hB : HasTypeStmtCI .breakK Γ body Γ}
            {hC : HasTypeStmtCI .continueK Γ body Γ}
            {hcond : BigStepValue σ c (.bool false)} =>
          fun hσ =>
            hσ)

      (while_true_normal_normal :=
        fun {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr}
            {body : CppStmt}
            {hc : HasValueType Γ c (.base .bool)}
            {hN : HasTypeStmtCI .normalK Γ body Γ}
            {hB : HasTypeStmtCI .breakK Γ body Γ}
            {hC : HasTypeStmtCI .continueK Γ body Γ}
            {hcond : BigStepValue σ c (.bool true)}
            {hbody : BigStepStmt σ body .normal σ₁}
            {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂}
            (hcompBody : StmtControlCompatible hN hbody)
            (hcompTail :
              StmtControlCompatible
                (HasTypeStmtCI.while_normal hc hN hB hC)
                htail)
            (ihBody :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Γ σ₁)
            (ihTail :
              ScopedTypedStateConcrete Γ σ₁ →
              ScopedTypedStateConcrete Γ σ₂) =>
          fun hσ =>
            ihTail (ihBody hσ))

      (while_true_break :=
        fun {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr}
            {body : CppStmt}
            {hc : HasValueType Γ c (.base .bool)}
            {hN : HasTypeStmtCI .normalK Γ body Γ}
            {hB : HasTypeStmtCI .breakK Γ body Γ}
            {hC : HasTypeStmtCI .continueK Γ body Γ}
            {hcond : BigStepValue σ c (.bool true)}
            {hbody : BigStepStmt σ body .breakResult σ₁}
            (hcompBody : StmtControlCompatible hB hbody)
            (ihBody :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Γ σ₁) =>
          ihBody)

      (while_true_continue_normal :=
        fun {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr}
            {body : CppStmt}
            {hc : HasValueType Γ c (.base .bool)}
            {hN : HasTypeStmtCI .normalK Γ body Γ}
            {hB : HasTypeStmtCI .breakK Γ body Γ}
            {hC : HasTypeStmtCI .continueK Γ body Γ}
            {hcond : BigStepValue σ c (.bool true)}
            {hbody : BigStepStmt σ body .continueResult σ₁}
            {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂}
            (hcompBody : StmtControlCompatible hC hbody)
            (hcompTail :
              StmtControlCompatible
                (HasTypeStmtCI.while_normal hc hN hB hC)
                htail)
            (ihBody :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Γ σ₁)
            (ihTail :
              ScopedTypedStateConcrete Γ σ₁ →
              ScopedTypedStateConcrete Γ σ₂) =>
          fun hσ =>
            ihTail (ihBody hσ))

      (while_true_normal_return :=
        fun {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr}
            {body : CppStmt}
            {hc : HasValueType Γ c (.base .bool)}
            {hN : HasTypeStmtCI .normalK Γ body Γ}
            {hB : HasTypeStmtCI .breakK Γ body Γ}
            {hC : HasTypeStmtCI .continueK Γ body Γ}
            {hR : HasTypeStmtCI .returnK Γ body Δ}
            {hcond : BigStepValue σ c (.bool true)}
            {rv : Option Value}
            {hbody : BigStepStmt σ body .normal σ₁}
            {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂}
            (hcompBody : StmtControlCompatible hN hbody)
            (hcompTail :
              StmtControlCompatible
                (HasTypeStmtCI.while_return hc hN hB hC hR)
                htail)
            (ihBody :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Γ σ₁)
            (ihTail :
              ScopedTypedStateConcrete Γ σ₁ →
              ScopedTypedStateConcrete Δ σ₂) =>
          fun hσ =>
            ihTail (ihBody hσ))

      (while_true_continue_return :=
        fun {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr}
            {body : CppStmt}
            {hc : HasValueType Γ c (.base .bool)}
            {hN : HasTypeStmtCI .normalK Γ body Γ}
            {hB : HasTypeStmtCI .breakK Γ body Γ}
            {hC : HasTypeStmtCI .continueK Γ body Γ}
            {hR : HasTypeStmtCI .returnK Γ body Δ}
            {hcond : BigStepValue σ c (.bool true)}
            {rv : Option Value}
            {hbody : BigStepStmt σ body .continueResult σ₁}
            {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂}
            (hcompBody : StmtControlCompatible hC hbody)
            (hcompTail :
              StmtControlCompatible
                (HasTypeStmtCI.while_return hc hN hB hC hR)
                htail)
            (ihBody :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Γ σ₁)
            (ihTail :
              ScopedTypedStateConcrete Γ σ₁ →
              ScopedTypedStateConcrete Δ σ₂) =>
          fun hσ =>
            ihTail (ihBody hσ))

      (while_true_return :=
        fun {Γ Δ : TypeEnv} {σ σ₁ : State} {c : ValExpr}
            {body : CppStmt} {rv : Option Value}
            {hc : HasValueType Γ c (.base .bool)}
            {hN : HasTypeStmtCI .normalK Γ body Γ}
            {hB : HasTypeStmtCI .breakK Γ body Γ}
            {hC : HasTypeStmtCI .continueK Γ body Γ}
            {hR : HasTypeStmtCI .returnK Γ body Δ}
            {hcond : BigStepValue σ c (.bool true)}
            {hbody : BigStepStmt σ body (.returnResult rv) σ₁}
            (hcompBody : StmtControlCompatible hR hbody)
            (ihBody :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ₁) =>
          ihBody)

      (block :=
        fun {k : ControlKind} {Γ Θ : TypeEnv} {ss : StmtBlock}
            {σ σ₀ σ₁ σ₂ : State} {ctrl : CtrlResult}
            {htyB : HasTypeBlockCI k (pushTypeScope Γ) ss Θ}
            {hopen : OpenScope σ σ₀}
            {hbody : BigStepBlock σ₀ ss ctrl σ₁}
            {hclose : CloseScope σ₁ σ₂}
            (hcompBody : BlockControlCompatible htyB hbody)
            (ihBody :
              ScopedTypedStateConcrete (pushTypeScope Γ) σ₀ →
              ScopedTypedStateConcrete Θ σ₁) =>
          fun hσ =>
            have hσ₀ : ScopedTypedStateConcrete (pushTypeScope Γ) σ₀ :=
              openScope_preserves_scoped_typed_state_concrete hσ hopen
            have hσ₁ : ScopedTypedStateConcrete Θ σ₁ :=
              ihBody hσ₀
            have hExt : TopFrameExtensionOf Γ Θ :=
              block_ci_topFrameExtension htyB
            closeScope_preserves_outer_from_topFrameExtension
              hExt hσ₁ hclose)

      (nil :=
        fun {x : TypeEnv} {x_1 : State} {Γ₀ : TypeEnv} {σ₀ : State} =>
          fun hσ =>
            hσ)

      (cons_normal :=
        fun {k : ControlKind} {Γ Θ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock}
            {σ σ₁ σ₂ : State} {ctrl : CtrlResult}
            {htyS : HasTypeStmtCI .normalK Γ s Θ}
            {htyT : HasTypeBlockCI k Θ ss Δ}
            {hstepS : BigStepStmt σ s .normal σ₁}
            {hstepT : BigStepBlock σ₁ ss ctrl σ₂}
            (hcompS : StmtControlCompatible htyS hstepS)
            (hcompT : BlockControlCompatible htyT hstepT)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Θ σ₁)
            (ihT :
              ScopedTypedStateConcrete Θ σ₁ →
              ScopedTypedStateConcrete Δ σ₂) =>
          fun hσ =>
            ihT (ihS hσ))

      (cons_break :=
        fun {x : StmtBlock} {Γ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock} {σ σ₁ : State}
            {htyS : HasTypeStmtCI .breakK Γ s Δ}
            {hstepS : BigStepStmt σ s .breakResult σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ₁) =>
          ihS)

      (cons_continue :=
        fun {x : StmtBlock} {Γ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock} {σ σ₁ : State}
            {htyS : HasTypeStmtCI .continueK Γ s Δ}
            {hstepS : BigStepStmt σ s .continueResult σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ₁) =>
          ihS)

      (cons_return :=
        fun {x : StmtBlock} {Γ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock} {σ σ₁ : State} {rv : Option Value}
            {htyS : HasTypeStmtCI .returnK Γ s Δ}
            {hstepS : BigStepStmt σ s (.returnResult rv) σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (ihS :
              ScopedTypedStateConcrete Γ σ →
              ScopedTypedStateConcrete Δ σ₁) =>
          ihS)

      hcomp


/--
Block control-compatible execution preserves scoped/typed state,
without requiring block readiness.

This theorem uses `BlockControlCompatible.rec` directly.  For statement head
steps in block cons cases, it reuses the statement theorem above.
-/
theorem block_control_preserves_scoped_typed_state_of_compatible_noReady
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  exact
    BlockControlCompatible.rec
      (motive_1 :=
        fun {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
            {σ : State} {ctrl : CtrlResult} {σ' : State}
            (hty : HasTypeStmtCI k Γ s Δ)
            (hstep : BigStepStmt σ s ctrl σ')
            (_hcomp : StmtControlCompatible hty hstep) =>
          True)
      (motive_2 :=
        fun {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
            {σ : State} {ctrl : CtrlResult} {σ' : State}
            (hty : HasTypeBlockCI k Γ ss Δ)
            (hstep : BigStepBlock σ ss ctrl σ')
            (_hcomp : BlockControlCompatible hty hstep) =>
          ScopedTypedStateConcrete Γ σ →
          ScopedTypedStateConcrete Δ σ')

      (skip := by
        intros
        trivial)

      (exprStmt := by
        intros
        trivial)

      (assign := by
        intros
        trivial)

      (declareObjNone := by
        intros
        trivial)

      (declareObjSome := by
        intros
        trivial)

      (declareRef := by
        intros
        trivial)

      (breakStmt := by
        intros
        trivial)

      (continueStmt := by
        intros
        trivial)

      (returnNone := by
        intros
        trivial)

      (returnSome := by
        intros
        trivial)

      (seq_normal := by
        intros
        trivial)

      (seq_break := by
        intros
        trivial)

      (seq_continue := by
        intros
        trivial)

      (seq_return := by
        intros
        trivial)

      (ite_true := by
        intros
        trivial)

      (ite_false := by
        intros
        trivial)

      (while_false_normal := by
        intros
        trivial)

      (while_true_normal_normal := by
        intros
        trivial)

      (while_true_break := by
        intros
        trivial)

      (while_true_continue_normal := by
        intros
        trivial)

      (while_true_normal_return := by
        intros
        trivial)

      (while_true_continue_return := by
        intros
        trivial)

      (while_true_return := by
        intros
        trivial)

      (block := by
        intros
        trivial)

      (nil :=
        fun {x : TypeEnv} {x_1 : State} {Γ₀ : TypeEnv} {σ₀ : State} =>
          fun hσ =>
            hσ)

      (cons_normal :=
        fun {k : ControlKind} {Γ Θ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock}
            {σ σ₁ σ₂ : State} {ctrl : CtrlResult}
            {htyS : HasTypeStmtCI .normalK Γ s Θ}
            {htyT : HasTypeBlockCI k Θ ss Δ}
            {hstepS : BigStepStmt σ s .normal σ₁}
            {hstepT : BigStepBlock σ₁ ss ctrl σ₂}
            (hcompS : StmtControlCompatible htyS hstepS)
            (hcompT : BlockControlCompatible htyT hstepT)
            (_ihS : True)
            (ihT :
              ScopedTypedStateConcrete Θ σ₁ →
              ScopedTypedStateConcrete Δ σ₂) =>
          fun hσ =>
            have hσ₁ : ScopedTypedStateConcrete Θ σ₁ :=
              stmt_control_preserves_scoped_typed_state_of_compatible_noReady
                hcompS hσ
            ihT hσ₁)

      (cons_break :=
        fun {x : StmtBlock} {Γ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock} {σ σ₁ : State}
            {htyS : HasTypeStmtCI .breakK Γ s Δ}
            {hstepS : BigStepStmt σ s .breakResult σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (_ihS : True) =>
          fun hσ =>
            stmt_control_preserves_scoped_typed_state_of_compatible_noReady
              hcompS hσ)

      (cons_continue :=
        fun {x : StmtBlock} {Γ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock} {σ σ₁ : State}
            {htyS : HasTypeStmtCI .continueK Γ s Δ}
            {hstepS : BigStepStmt σ s .continueResult σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (_ihS : True) =>
          fun hσ =>
            stmt_control_preserves_scoped_typed_state_of_compatible_noReady
              hcompS hσ)

      (cons_return :=
        fun {x : StmtBlock} {Γ Δ : TypeEnv} {s : CppStmt}
            {ss : StmtBlock} {σ σ₁ : State} {rv : Option Value}
            {htyS : HasTypeStmtCI .returnK Γ s Δ}
            {hstepS : BigStepStmt σ s (.returnResult rv) σ₁}
            (hcompS : StmtControlCompatible htyS hstepS)
            (_ihS : True) =>
          fun hσ =>
            stmt_control_preserves_scoped_typed_state_of_compatible_noReady
              hcompS hσ)

      hcomp


/-- Normal statement wrapper. -/
theorem stmt_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    {hty : HasTypeStmtCI .normalK Γ s Δ}
    {hstep : BigStepStmt σ s .normal σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  exact
    stmt_control_preserves_scoped_typed_state_of_compatible_noReady
      hcomp


/-- Normal block wrapper. -/
theorem block_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    {hty : HasTypeBlockCI .normalK Γ ss Δ}
    {hstep : BigStepBlock σ ss .normal σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  exact
    block_control_preserves_scoped_typed_state_of_compatible_noReady
      hcomp

--旧Proof.Preservation.StmtControlKernelにあった公開用のtheorem

theorem stmt_control_preserves_scoped_typed_state_of_compatible
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ _hready
  exact
    stmt_control_preserves_scoped_typed_state_of_compatible_noReady
      hcomp hσ

theorem block_control_preserves_scoped_typed_state_of_compatible
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' := by
  intro hσ _hready
  exact
    block_control_preserves_scoped_typed_state_of_compatible_noReady
      hcomp hσ


end Cpp
