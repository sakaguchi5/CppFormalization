import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StrongThinSeparatedCondReplay
import CppFormalization.Cpp2.Closure.Internal.ResidualTransportStableFragment
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
Residual transport fragment strengthened by the theoremized strong thin-separated
condition replay across a specific head assignment `q := rhs`.

This file does not try to solve every residual case. It isolates the next honest
gain after `StrongThinSeparatedCondReplay`:

- keep the old replay-stable read-place restriction on suffix *places*;
- replace condition/value-expression replay by the stronger assignment-centered
  deref-aware fragment;
- recover seq/block residual boundaries for the concrete head
  `.assign q rhs`.

So this is the direct bridge from the local separation story back into the
residual transport story.
-/


/- =========================================================
   1. Assignment-headed transportable suffix fragment
   ========================================================= -/

mutual

inductive AssignHeadTransportableStmt :
    TypeEnv → State → PlaceExpr → ValExpr → CppStmt → Prop where
  | skip {Γ σ q rhs} :
      AssignHeadTransportableStmt Γ σ q rhs .skip
  | exprStmt {Γ σ q rhs e τ} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmt Γ σ q rhs (.exprStmt e)
  | assign {Γ σ q rhs p e τ} :
      ReplayStableReadPlace p →
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmt Γ σ q rhs (.assign p e)
  | seq {Γ σ q rhs s t} :
      AssignHeadTransportableStmt Γ σ q rhs s →
      AssignHeadTransportableStmt Γ σ q rhs t →
      AssignHeadTransportableStmt Γ σ q rhs (.seq s t)
  | ite {Γ σ q rhs c s t} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmt Γ σ q rhs s →
      AssignHeadTransportableStmt Γ σ q rhs t →
      AssignHeadTransportableStmt Γ σ q rhs (.ite c s t)
  | whileStmt {Γ σ q rhs c body} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmt Γ σ q rhs body →
      AssignHeadTransportableStmt Γ σ q rhs (.whileStmt c body)
  | block {Γ σ q rhs ss} :
      AssignHeadTransportableBlock (pushTypeScope Γ) (pushScope σ) q rhs ss →
      AssignHeadTransportableStmt Γ σ q rhs (.block ss)
  | breakStmt {Γ σ q rhs} :
      AssignHeadTransportableStmt Γ σ q rhs .breakStmt
  | continueStmt {Γ σ q rhs} :
      AssignHeadTransportableStmt Γ σ q rhs .continueStmt
  | returnNone {Γ σ q rhs} :
      AssignHeadTransportableStmt Γ σ q rhs (.returnStmt none)
  | returnSome {Γ σ q rhs e τ} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmt Γ σ q rhs (.returnStmt (some e))

inductive AssignHeadTransportableBlock :
    TypeEnv → State → PlaceExpr → ValExpr → StmtBlock → Prop where
  | nil {Γ σ q rhs} :
      AssignHeadTransportableBlock Γ σ q rhs .nil
  | cons {Γ σ q rhs s ss} :
      AssignHeadTransportableStmt Γ σ q rhs s →
      AssignHeadTransportableBlock Γ σ q rhs ss →
      AssignHeadTransportableBlock Γ σ q rhs (.cons s ss)

end


/- =========================================================
   1.5 Push-scope stability bridges used by the block case
   ========================================================= -/

mutual

theorem hasPlaceType_pushTypeScope_frag
    {Γ : TypeEnv} {p : PlaceExpr} {τ : CppType} :
    HasPlaceType Γ p τ →
    HasPlaceType (pushTypeScope Γ) p τ := by
  intro h
  cases h with
  | var hlookup =>
      exact .var (by
        simpa [lookupDecl, lookupDeclFrames, pushTypeScope, emptyTypeFrame] using hlookup)
  | deref hv =>
      exact .deref (hasValueType_pushTypeScope_frag hv)

theorem hasValueType_pushTypeScope_frag
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    HasValueType (pushTypeScope Γ) e τ := by
  intro h
  cases h with
  | litBool =>
      exact .litBool
  | litInt =>
      exact .litInt
  | load hp =>
      exact .load (hasPlaceType_pushTypeScope_frag hp)
  | addrOf hp =>
      exact .addrOf (hasPlaceType_pushTypeScope_frag hp)
  | add h1 h2 =>
      exact .add
        (hasValueType_pushTypeScope_frag h1)
        (hasValueType_pushTypeScope_frag h2)
  | sub h1 h2 =>
      exact .sub
        (hasValueType_pushTypeScope_frag h1)
        (hasValueType_pushTypeScope_frag h2)
  | mul h1 h2 =>
      exact .mul
        (hasValueType_pushTypeScope_frag h1)
        (hasValueType_pushTypeScope_frag h2)
  | eq h1 h2 =>
      exact .eq
        (hasValueType_pushTypeScope_frag h1)
        (hasValueType_pushTypeScope_frag h2)
  | lt h1 h2 =>
      exact .lt
        (hasValueType_pushTypeScope_frag h1)
        (hasValueType_pushTypeScope_frag h2)
  | not h =>
      exact .not (hasValueType_pushTypeScope_frag h)

end

mutual

theorem bigStepPlace_pushScope_frag
    {σ : State} {p : PlaceExpr} {a : Nat} :
    BigStepPlace σ p a →
    BigStepPlace (pushScope σ) p a := by
  intro h
  cases h with
  | varObject hlookup =>
      exact .varObject (by
        simpa [lookupBinding, lookupBindingFrames, pushScope, emptyScopeFrame] using hlookup)
  | varRef hlookup =>
      exact .varRef (by
        simpa [lookupBinding, lookupBindingFrames, pushScope, emptyScopeFrame] using hlookup)
  | deref hv hheap halive =>
      exact .deref
        (bigStepValue_pushScope_frag hv)
        (by simpa [pushScope] using hheap)
        halive

theorem bigStepValue_pushScope_frag
    {σ : State} {e : ValExpr} {v : Value} :
    BigStepValue σ e v →
    BigStepValue (pushScope σ) e v := by
  intro h
  cases h with
  | litBool =>
      exact .litBool
  | litInt =>
      exact .litInt
  | load hp hheap halive hval =>
      exact .load
        (bigStepPlace_pushScope_frag hp)
        (by simpa [pushScope] using hheap)
        halive
        hval
  | addrOf hp =>
      exact .addrOf (bigStepPlace_pushScope_frag hp)
  | add h1 h2 =>
      exact .add
        (bigStepValue_pushScope_frag h1)
        (bigStepValue_pushScope_frag h2)
  | sub h1 h2 =>
      exact .sub
        (bigStepValue_pushScope_frag h1)
        (bigStepValue_pushScope_frag h2)
  | mul h1 h2 =>
      exact .mul
        (bigStepValue_pushScope_frag h1)
        (bigStepValue_pushScope_frag h2)
  | eq h1 h2 =>
      exact .eq
        (bigStepValue_pushScope_frag h1)
        (bigStepValue_pushScope_frag h2)
  | lt h1 h2 =>
      exact .lt
        (bigStepValue_pushScope_frag h1)
        (bigStepValue_pushScope_frag h2)
  | not h =>
      exact .not (bigStepValue_pushScope_frag h)

end


def ThinSeparatedWitness.pushScope_frag
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    ThinSeparatedWitness Γ σ q rhs e τ →
    ThinSeparatedWitness (pushTypeScope Γ) (pushScope σ) q rhs e τ
  | w =>
      { ptrType := hasValueType_pushTypeScope_frag w.ptrType
        srcStable := w.srcStable
        writeAddr := w.writeAddr
        writesQ := bigStepPlace_pushScope_frag w.writesQ
        targetSeparated := by
          intro a hvalPush
          exact w.targetSeparated (bigStepValue_of_pushScope hvalPush) }

def LoadThinSeparatedWitness.pushScope_frag
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    LoadThinSeparatedWitness Γ σ q rhs p τ →
    LoadThinSeparatedWitness (pushTypeScope Γ) (pushScope σ) q rhs p τ
  | w =>
      { base := w.base.pushScope_frag
        sourceSeparated := by
          intro aSrc hplacePush
          exact w.sourceSeparated (bigStepPlace_of_pushScope hplacePush) }

def StrongThinSeparatedWitness.pushScope_frag
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    StrongThinSeparatedWitness Γ σ q rhs e τ →
    StrongThinSeparatedWitness (pushTypeScope Γ) (pushScope σ) q rhs e τ
  | .addrOf w => .addrOf w.pushScope_frag
  | .load w => .load w.pushScope_frag

theorem strongThinSeparatedCondExpr_pushScope_frag
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs e : ValExpr} {τ : CppType} :
    StrongThinSeparatedCondExpr Γ σ q rhs e τ →
    StrongThinSeparatedCondExpr (pushTypeScope Γ) (pushScope σ) q rhs e τ := by
  intro h
  induction h with
  | base hbase hty =>
      exact .base hbase (hasValueType_pushTypeScope_frag hty)
  | loadDeref hw =>
      exact .loadDeref hw.pushScope_frag
  | addrOfDeref hw =>
      exact .addrOfDeref hw.pushScope_frag
  | add h1 h2 ih1 ih2 =>
      exact .add ih1 ih2
  | sub h1 h2 ih1 ih2 =>
      exact .sub ih1 ih2
  | mul h1 h2 ih1 ih2 =>
      exact .mul ih1 ih2
  | eq h1 h2 ih1 ih2 =>
      exact .eq ih1 ih2
  | lt h1 h2 ih1 ih2 =>
      exact .lt ih1 ih2
  | not h ih =>
      exact .not ih

theorem scoped_typed_state_concrete_pushScope_frag
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete (pushTypeScope Γ) (pushScope σ) := by
  intro h
  refine
    { frameDepth := by
        unfold frameDepthAgreement at *
        simpa [pushTypeScope, pushScope] using congrArg Nat.succ h.frameDepth

      namesExact := by
        intro k Γfr σfr hkΓ hkσ
        cases k with
        | zero =>
            have hΓfr : Γfr = emptyTypeFrame := by
              simpa [pushTypeScope, emptyTypeFrame] using hkΓ.symm
            have hσfr : σfr = emptyScopeFrame := by
              simpa [pushScope, emptyScopeFrame] using hkσ.symm
            subst Γfr
            subst σfr
            constructor
            · intro x d hdecl
              have : False := by
                simp [emptyTypeFrame] at hdecl
              exact False.elim this
            · intro x b hbind
              have : False := by
                simp [emptyScopeFrame] at hbind
              exact False.elim this
        | succ k =>
            have hkΓOld : Γ.scopes[k]? = some Γfr := by
              simpa [pushTypeScope] using hkΓ
            have hkσOld : σ.scopes[k]? = some σfr := by
              simpa [pushScope] using hkσ
            exact h.namesExact k Γfr σfr hkΓOld hkσOld

      shadowing := by
        intro x d hdecl
        have hdeclOld : lookupDecl Γ x = some d := by
          simpa [lookupDecl, lookupDeclFrames, pushTypeScope, emptyTypeFrame] using hdecl
        rcases h.shadowing x d hdeclOld with ⟨b, hb, hmatch⟩
        refine ⟨b, ?_, hmatch⟩
        simpa [lookupBinding, lookupBindingFrames, pushScope, emptyScopeFrame] using hb

      objectDeclRealized := by
        intro k x τ hdecl
        cases k with
        | zero =>
            have : False := by
              simp [typeFrameDeclObject, pushTypeScope, emptyTypeFrame] at hdecl
            exact False.elim this
        | succ k =>
            have hdeclOld : typeFrameDeclObject Γ k x τ := by
              simpa [typeFrameDeclObject, pushTypeScope] using hdecl
            rcases h.objectDeclRealized hdeclOld with ⟨a, hbind, hown, hlive⟩
            refine ⟨a, ?_, ?_, ?_⟩
            · simpa [runtimeFrameBindsObject, pushScope] using hbind
            · simpa [runtimeFrameOwnsAddress, pushScope] using hown
            · simpa [heapLiveTypedAt, pushScope] using hlive

      refDeclRealized := by
        intro k x τ hdecl
        cases k with
        | zero =>
            have : False := by
              simp [typeFrameDeclRef, pushTypeScope, emptyTypeFrame] at hdecl
            exact False.elim this
        | succ k =>
            have hdeclOld : typeFrameDeclRef Γ k x τ := by
              simpa [typeFrameDeclRef, pushTypeScope] using hdecl
            rcases h.refDeclRealized hdeclOld with ⟨a, hbind, hlive⟩
            refine ⟨a, ?_, ?_⟩
            · simpa [runtimeFrameBindsRef, pushScope] using hbind
            · simpa [heapLiveTypedAt, pushScope] using hlive

      objectBindingSound := by
        intro k x τ a hbind
        cases k with
        | zero =>
            have : False := by
              simp [runtimeFrameBindsObject, pushScope, emptyScopeFrame] at hbind
            exact False.elim this
        | succ k =>
            have hbindOld : runtimeFrameBindsObject σ k x τ a := by
              simpa [runtimeFrameBindsObject, pushScope] using hbind
            rcases h.objectBindingSound hbindOld with ⟨hown, hlive⟩
            refine ⟨?_, ?_⟩
            · simpa [runtimeFrameOwnsAddress, pushScope] using hown
            · simpa [heapLiveTypedAt, pushScope] using hlive

      refBindingSound := by
        intro k x τ a hbind
        cases k with
        | zero =>
            have : False := by
              simp [runtimeFrameBindsRef, pushScope, emptyScopeFrame] at hbind
            exact False.elim this
        | succ k =>
            have hbindOld : runtimeFrameBindsRef σ k x τ a := by
              simpa [runtimeFrameBindsRef, pushScope] using hbind
            simpa [heapLiveTypedAt, pushScope] using h.refBindingSound hbindOld

      ownedAddressNamed := by
        intro k a hown
        cases k with
        | zero =>
            have : False := by
              simp [runtimeFrameOwnsAddress, pushScope, emptyScopeFrame] at hown
            exact False.elim this
        | succ k =>
            have hownOld : runtimeFrameOwnsAddress σ k a := by
              simpa [runtimeFrameOwnsAddress, pushScope] using hown
            rcases h.ownedAddressNamed hownOld with ⟨x, τ, hbind⟩
            exact ⟨x, τ, by simpa [runtimeFrameBindsObject, pushScope] using hbind⟩

      refsNotOwned := by
        intro k fr x τ a hk hbind hlocal
        cases k with
        | zero =>
            have hfr : fr = emptyScopeFrame := by
              simpa [pushScope, emptyScopeFrame] using hk.symm
            subst fr
            have : False := by
              simp [emptyScopeFrame] at hbind
            exact False.elim this
        | succ k =>
            have hkOld : σ.scopes[k]? = some fr := by
              simpa [pushScope] using hk
            exact h.refsNotOwned k fr x τ a hkOld hbind hlocal

      objectsOwned := by
        intro k x τ a hbind
        cases k with
        | zero =>
            have : False := by
              simp [runtimeFrameBindsObject, pushScope, emptyScopeFrame] at hbind
            exact False.elim this
        | succ k =>
            have hbindOld : runtimeFrameBindsObject σ k x τ a := by
              simpa [runtimeFrameBindsObject, pushScope] using hbind
            have hownOld := h.objectsOwned k x τ a hbindOld
            simpa [runtimeFrameOwnsAddress, pushScope] using hownOld

      ownedNoDupPerFrame := by
        intro k fr hk
        cases k with
        | zero =>
            have hfr : fr = emptyScopeFrame := by
              simpa [pushScope, emptyScopeFrame] using hk.symm
            subst fr
            simp [emptyScopeFrame]
        | succ k =>
            have hkOld : σ.scopes[k]? = some fr := by
              simpa [pushScope] using hk
            exact h.ownedNoDupPerFrame k fr hkOld

      ownedDisjoint := ownedAddressesDisjoint_pushScope h.ownedDisjoint

      ownedNamed := by
        intro k a hown
        cases k with
        | zero =>
            have : False := by
              simp [runtimeFrameOwnsAddress, pushScope, emptyScopeFrame] at hown
            exact False.elim this
        | succ k =>
            have hownOld : runtimeFrameOwnsAddress σ k a := by
              simpa [runtimeFrameOwnsAddress, pushScope] using hown
            rcases h.ownedNamed k a hownOld with ⟨x, τ, hbind⟩
            exact ⟨x, τ, by simpa [runtimeFrameBindsObject, pushScope] using hbind⟩

      heapStoredValuesTyped := by
        simpa [heapInitializedValuesTyped, pushScope] using h.heapStoredValuesTyped

      nextFresh := nextIsFreshForOwnedHeap_pushScope h.nextFresh

      refTargetsAvoidInnerOwned := by
        intro k x τ a j hbind hj
        cases k with
        | zero =>
            have : False := by
              simp [runtimeFrameBindsRef, pushScope, emptyScopeFrame] at hbind
            exact False.elim this
        | succ k =>
            cases j with
            | zero =>
                intro hown
                have : False := by
                  simp [runtimeFrameOwnsAddress, pushScope, emptyScopeFrame] at hown
                exact False.elim this
            | succ j =>
                have hbindOld : runtimeFrameBindsRef σ k x τ a := by
                  simpa [runtimeFrameBindsRef, pushScope] using hbind
                have hjOld : j < k := Nat.lt_of_succ_lt_succ hj
                have havoidOld := h.refTargetsAvoidInnerOwned hbindOld hjOld
                intro hown
                have hownOld : runtimeFrameOwnsAddress σ j a := by
                  simpa [runtimeFrameOwnsAddress, pushScope] using hown
                exact havoidOld hownOld }

theorem assigns_pushScope_frag
    {σ σ' : State} {p : PlaceExpr} {v : Value} :
    Assigns σ p v σ' →
    Assigns (pushScope σ) p v (pushScope σ') := by
  intro h
  rcases h with ⟨a, c, hp, hheap, halive, hcompat, rfl⟩
  refine ⟨a, c, bigStepPlace_pushScope_frag hp, ?_, halive, hcompat, ?_⟩
  · simpa [pushScope] using hheap
  · simp [writeHeap, pushScope]

theorem bigStepStmt_assign_pushScope_frag
    {σ σ' : State} {q : PlaceExpr} {rhs : ValExpr} :
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BigStepStmt (pushScope σ) (.assign q rhs) .normal (pushScope σ') := by
  intro h
  cases h with
  | assign hval hassign =>
      exact .assign
        (bigStepValue_pushScope_frag hval)
        (assigns_pushScope_frag hassign)

mutual

theorem assign_head_transportable_stmt_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} {st : CppStmt}
    (h : AssignHeadTransportableStmt Γ σ q rhs st) :
    AssignHeadTransportableStmt (pushTypeScope Γ) (pushScope σ) q rhs st := by
  match h with
  | .skip =>
      exact .skip
  | .exprStmt hc hty =>
      exact .exprStmt
        (strongThinSeparatedCondExpr_pushScope_frag hc)
        (hasValueType_pushTypeScope_frag hty)
  | .assign hp hc hty =>
      exact .assign
        hp
        (strongThinSeparatedCondExpr_pushScope_frag hc)
        (hasValueType_pushTypeScope_frag hty)
  | .seq hs ht =>
      exact .seq
        (assign_head_transportable_stmt_pushScope hs)
        (assign_head_transportable_stmt_pushScope ht)
  | .ite hc hs ht =>
      exact .ite
        (strongThinSeparatedCondExpr_pushScope_frag hc)
        (assign_head_transportable_stmt_pushScope hs)
        (assign_head_transportable_stmt_pushScope ht)
  | .whileStmt hc hbody =>
      exact .whileStmt
        (strongThinSeparatedCondExpr_pushScope_frag hc)
        (assign_head_transportable_stmt_pushScope hbody)
  | .block hblock =>
      exact .block
        (assign_head_transportable_block_pushScope hblock)
  | .breakStmt =>
      exact .breakStmt
  | .continueStmt =>
      exact .continueStmt
  | .returnNone =>
      exact .returnNone
  | .returnSome hc hty =>
      exact .returnSome
        (strongThinSeparatedCondExpr_pushScope_frag hc)
        (hasValueType_pushTypeScope_frag hty)

theorem assign_head_transportable_block_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock}
    (h : AssignHeadTransportableBlock Γ σ q rhs ss) :
    AssignHeadTransportableBlock (pushTypeScope Γ) (pushScope σ) q rhs ss := by
  match h with
  | .nil =>
      exact .nil
  | .cons hs hss =>
      exact .cons
        (assign_head_transportable_stmt_pushScope hs)
        (assign_head_transportable_block_pushScope hss)

end


/- =========================================================
   2. Replay across the fixed head assignment
   ========================================================= -/

mutual

theorem assign_head_transportable_stmt_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {target : CppStmt}
    (htarget : AssignHeadTransportableStmt Γ σ q rhs target) :
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ target →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' target := by
  intro hσ' hready hstep
  match htarget with
  | .skip =>
      exact .skip
  | .exprStmt hc hty_hc =>
      match hready with
      | .exprStmt hty_ready heready =>
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact .exprStmt hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)
  | .assign hp hc hty_hc =>
      match hready with
      | .assign hpty hpready hvty_ready heready =>
          have heq := hasValueType_unique hvty_ready hty_hc
          subst heq
          exact .assign
            hpty
            (replay_stable_read_place_ready_after_assign hp hσ' hpready hstep)
            hvty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)
  | .seq hs ht =>
      match hready with
      | .seq hreadyS hreadyT =>
          exact .seq
            (assign_head_transportable_stmt_ready_after_assign_head
              hs hσ' hreadyS hstep)
            (assign_head_transportable_stmt_ready_after_assign_head
              ht hσ' hreadyT hstep)
  | .ite hc hs ht =>
      match hready with
      | .ite hcty hcready hreadyS hreadyT =>
          exact .ite
            hcty
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' hcready hstep)
            (assign_head_transportable_stmt_ready_after_assign_head
              hs hσ' hreadyS hstep)
            (assign_head_transportable_stmt_ready_after_assign_head
              ht hσ' hreadyT hstep)
  | .whileStmt hc hbody =>
      match hready with
      | .whileStmt hcty hcready hreadyBody =>
          exact .whileStmt
            hcty
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' hcready hstep)
            (assign_head_transportable_stmt_ready_after_assign_head
              hbody hσ' hreadyBody hstep)
  | .block hblock =>
      match hready with
      | .block hreadyBlock =>
          have hσ'Push :
              ScopedTypedStateConcrete (pushTypeScope Γ) (pushScope σ') :=
            scoped_typed_state_concrete_pushScope_frag hσ'
          have hstepPush :
              BigStepStmt (pushScope σ) (.assign q rhs) .normal (pushScope σ') :=
            bigStepStmt_assign_pushScope_frag hstep
          exact .block
            (assign_head_transportable_block_ready_after_assign_head
              hblock hσ'Push hreadyBlock hstepPush)
  | .breakStmt =>
      exact .breakStmt
  | .continueStmt =>
      exact .continueStmt
  | .returnNone =>
      exact .returnNone
  | .returnSome hc hty_hc =>
      match hready with
      | .returnSome hty_ready heready =>
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact .returnSome
            hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)

theorem assign_head_transportable_block_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock}
    (hblock : AssignHeadTransportableBlock Γ σ q rhs ss) :
    ScopedTypedStateConcrete Γ σ' →
    BlockReadyConcrete Γ σ ss →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BlockReadyConcrete Γ σ' ss := by
  intro hσ' hready hstep
  match hblock with
  | .nil =>
      exact .nil
  | .cons hs hss =>
      match hready with
      | .cons hreadyS hreadySS =>
          exact .cons
            (assign_head_transportable_stmt_ready_after_assign_head
              hs hσ' hreadyS hstep)
            (assign_head_transportable_block_ready_after_assign_head
              hss hσ' hreadySS hstep)

end


/- =========================================================
   3. Residual boundary recovery for head = assign
   ========================================================= -/

theorem assign_stmt_env_preserving
    {Γ Δ : TypeEnv} {q : PlaceExpr} {rhs : ValExpr} :
    HasTypeStmtCI .normalK Γ (.assign q rhs) Δ →
    Δ = Γ := by
  intro hty
  cases hty
  rfl

theorem assign_head_transportable_right_seq_normal_preserves_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {t : CppStmt} :
    AssignHeadTransportableStmt Γ σ q rhs t →
    HasTypeStmtCI .normalK Γ (.seq (.assign q rhs) t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq (.assign q rhs) t) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro hright htySeq hσ hreadySeq hstepHead
  rcases seq_typing_data htySeq with ⟨Θ, htyHead, htyRight⟩
  have hΘ : Θ = Γ := by
    exact assign_stmt_env_preserving htyHead
  subst hΘ
  have hσ'Γ : ScopedTypedStateConcrete Θ σ' :=
    assign_stmt_normal_preserves_scoped_typed_state_concrete
      htyHead hσ (seq_ready_left hreadySeq) hstepHead
  have hreadyRight' : StmtReadyConcrete Θ σ' t :=
    assign_head_transportable_stmt_ready_after_assign_head
      hright hσ'Γ (seq_ready_right hreadySeq) hstepHead
  exact ⟨Θ, htyRight, hσ'Γ, hreadyRight'⟩

theorem assign_head_transportable_tail_cons_head_normal_preserves_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlock Γ σ q rhs ss →
    HasTypeBlockCI .normalK Γ (.cons (.assign q rhs) ss) Θ →
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ (.cons (.assign q rhs) ss) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ConsResidualBoundary Θ σ' ss := by
  intro htail hty hσ hready hstep
  rcases cons_block_typing_data hty with ⟨Ξ, htyHead, htyTail⟩
  have hΞ : Ξ = Γ := by
    exact assign_stmt_env_preserving htyHead
  subst hΞ
  have hσ'Γ : ScopedTypedStateConcrete Ξ σ' :=
    assign_stmt_normal_preserves_scoped_typed_state_concrete
      htyHead hσ (cons_block_ready_head hready) hstep
  have hreadyTail' : BlockReadyConcrete Ξ σ' ss :=
    assign_head_transportable_block_ready_after_assign_head
      htail hσ'Γ (cons_block_ready_tail hready) hstep
  exact ⟨Ξ, htyTail, hσ'Γ, hreadyTail'⟩

end Cpp
