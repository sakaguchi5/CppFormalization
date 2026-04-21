import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness

namespace Cpp

mutual

theorem hasPlaceType_pushTypeScope
    {Γ : TypeEnv} {p : PlaceExpr} {τ : CppType} :
    HasPlaceType Γ p τ →
    HasPlaceType (pushTypeScope Γ) p τ := by
  intro h
  cases h with
  | var hlookup =>
      exact .var (by
        simpa [lookupDecl, lookupDeclFrames, pushTypeScope, emptyTypeFrame] using hlookup)
  | deref hv =>
      exact .deref (hasValueType_pushTypeScope hv)

theorem hasValueType_pushTypeScope
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    HasValueType (pushTypeScope Γ) e τ := by
  intro h
  cases h with
  | litBool => exact .litBool
  | litInt => exact .litInt
  | load hp => exact .load (hasPlaceType_pushTypeScope hp)
  | addrOf hp => exact .addrOf (hasPlaceType_pushTypeScope hp)
  | add h1 h2 => exact .add (hasValueType_pushTypeScope h1) (hasValueType_pushTypeScope h2)
  | sub h1 h2 => exact .sub (hasValueType_pushTypeScope h1) (hasValueType_pushTypeScope h2)
  | mul h1 h2 => exact .mul (hasValueType_pushTypeScope h1) (hasValueType_pushTypeScope h2)
  | eq h1 h2 => exact .eq (hasValueType_pushTypeScope h1) (hasValueType_pushTypeScope h2)
  | lt h1 h2 => exact .lt (hasValueType_pushTypeScope h1) (hasValueType_pushTypeScope h2)
  | not h => exact .not (hasValueType_pushTypeScope h)

end

mutual

theorem bigStepPlace_pushScope
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
        (bigStepValue_pushScope hv)
        (by simpa [pushScope] using hheap)
        halive

theorem bigStepValue_pushScope
    {σ : State} {e : ValExpr} {v : Value} :
    BigStepValue σ e v →
    BigStepValue (pushScope σ) e v := by
  intro h
  cases h with
  | litBool => exact .litBool
  | litInt => exact .litInt
  | load hp hheap halive hval =>
      exact .load
        (bigStepPlace_pushScope hp)
        (by simpa [pushScope] using hheap)
        halive
        hval
  | addrOf hp => exact .addrOf (bigStepPlace_pushScope hp)
  | add h1 h2 => exact .add (bigStepValue_pushScope h1) (bigStepValue_pushScope h2)
  | sub h1 h2 => exact .sub (bigStepValue_pushScope h1) (bigStepValue_pushScope h2)
  | mul h1 h2 => exact .mul (bigStepValue_pushScope h1) (bigStepValue_pushScope h2)
  | eq h1 h2 => exact .eq (bigStepValue_pushScope h1) (bigStepValue_pushScope h2)
  | lt h1 h2 => exact .lt (bigStepValue_pushScope h1) (bigStepValue_pushScope h2)
  | not h => exact .not (bigStepValue_pushScope h)

end

theorem scoped_typed_state_concrete_pushScope
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

theorem assigns_pushScope
    {σ σ' : State} {p : PlaceExpr} {v : Value} :
    Assigns σ p v σ' →
    Assigns (pushScope σ) p v (pushScope σ') := by
  intro h
  rcases h with ⟨a, c, hp, hheap, halive, hcompat, rfl⟩
  refine ⟨a, c, bigStepPlace_pushScope hp, ?_, halive, hcompat, ?_⟩
  · simpa [pushScope] using hheap
  · simp [writeHeap, pushScope]

theorem bigStepStmt_assign_pushScope
    {σ σ' : State} {q : PlaceExpr} {rhs : ValExpr} :
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BigStepStmt (pushScope σ) (.assign q rhs) .normal (pushScope σ') := by
  intro h
  cases h with
  | assign hval hassign =>
      exact .assign
        (bigStepValue_pushScope hval)
        (assigns_pushScope hassign)

end Cpp
