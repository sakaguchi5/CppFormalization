import CppFormalization.Cpp2.Proof.Preservation.Assign.Preservation
import CppFormalization.Cpp2.Proof.Preservation.DeclareObject.Preservation
import CppFormalization.Cpp2.Proof.Preservation.DeclareRef.Preservation
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility

set_option maxHeartbeats 0

namespace Cpp

/-!
# Proof.Preservation.PrimitiveStmtNormalStateOnly

Experimental ready-free primitive preservation layer.

The purpose of this file is to test the route where preservation proves only
post-state scoped/typedness and therefore does not reconstruct residual
`StmtReadyConcrete` / `BlockReadyConcrete` facts.

Main idea:
- `ready` is an entry-safety/replay obligation.
- state preservation should follow the actual `BigStep` derivation.
- assignment preservation can avoid `PlaceReadyConcrete`: the operational
  `Assigns` payload already contains the written-cell value compatibility.
-/

namespace StateOnlyAssign

private theorem runtimeFrameBindsObject_writeHeap_iff_stateOnly
    {σ : State} {a : Nat} {c : Cell}
    {k : Nat} {x : Ident} {τ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (writeHeap σ a c) k x τ addr ↔
      runtimeFrameBindsObject σ k x τ addr := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsObject, writeHeap] using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsObject, writeHeap] using hk, hb⟩

private theorem runtimeFrameBindsRef_writeHeap_iff_stateOnly
    {σ : State} {a : Nat} {c : Cell}
    {k : Nat} {x : Ident} {τ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (writeHeap σ a c) k x τ addr ↔
      runtimeFrameBindsRef σ k x τ addr := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsRef, writeHeap] using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsRef, writeHeap] using hk, hb⟩

private theorem runtimeFrameOwnsAddress_writeHeap_iff_stateOnly
    {σ : State} {a : Nat} {c : Cell}
    {k : Nat} {addr : Nat} :
    runtimeFrameOwnsAddress (writeHeap σ a c) k addr ↔
      runtimeFrameOwnsAddress σ k addr := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hm⟩
    exact ⟨fr, by simpa [runtimeFrameOwnsAddress, writeHeap] using hk, hm⟩
  · rcases h with ⟨fr, hk, hm⟩
    exact ⟨fr, by simpa [runtimeFrameOwnsAddress, writeHeap] using hk, hm⟩

private theorem heapLiveTypedAt_writeHeap_preserved_stateOnly
    {σ : State} {aWrite : Nat} {cWrite : Cell}
    {a : Nat} {τ : CppType} :
    a = aWrite → cWrite.ty = τ → cWrite.alive = true →
    heapLiveTypedAt (writeHeap σ aWrite cWrite) a τ := by
  intro ha hty halive
  subst ha
  exact ⟨cWrite, by simp [writeHeap], hty, halive⟩

private theorem heapLiveTypedAt_assigns_preserved_stateOnly
    {σ σ' : State} {p : PlaceExpr} {v : Value}
    {a : Nat} {τ : CppType} :
    Assigns σ p v σ' →
    heapLiveTypedAt σ a τ →
    heapLiveTypedAt σ' a τ := by
  intro hassign hlive
  rcases hassign with ⟨a0, c0, _hplace, hheap0, halive0, _hcompat, rfl⟩
  by_cases ha : a = a0
  · subst ha
    rcases hlive with ⟨c, hheap, hty, halive⟩
    have hc : c = c0 := by
      rw [hheap0] at hheap
      injection hheap.symm
    subst hc
    exact heapLiveTypedAt_writeHeap_preserved_stateOnly
     rfl (by simpa using hty) (by simpa using halive0)
  · rcases hlive with ⟨c, hheap, hty, halive⟩
    refine ⟨c, ?_, hty, halive⟩
    simp [writeHeap, ha, hheap]

private theorem heapInitializedValuesTyped_after_assigns_stateOnly
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    Assigns σ p v σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ hassign
  rcases hassign with ⟨a0, c0, _hplace, hheap0, halive0, hcompat0, rfl⟩
  intro a c w hheap hval
  by_cases ha : a = a0
  · subst ha
    have hc : c = { c0 with value := some v } := by
      apply Option.some.inj
      simpa [writeHeap] using hheap.symm
    subst hc
    have hw : w = v := by
      apply Option.some.inj
      simpa using hval.symm
    subst hw
    simpa using hcompat0
  · have hheapOld : σ.heap a = some c := by
      simpa [writeHeap, ha] using hheap
    exact hσ.heapStoredValuesTyped a c w hheapOld hval

private theorem assigned_addr_ne_next_stateOnly
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    Assigns σ p v σ' →
    ∀ {a0 c0},
      BigStepPlace σ p a0 →
      σ.heap a0 = some c0 →
      a0 ≠ σ.next := by
  intro hσ _hassign a0 c0 _ hheap
  intro hEq
  subst hEq
  rcases hσ.nextFresh with ⟨hheapNone, _⟩
  rw [hheapNone] at hheap
  simp at hheap

private theorem framewiseDeclBindingExact_writeHeap_stateOnly
    {Γ : TypeEnv} {σ : State} {a : Nat} {c : Cell} :
    framewiseDeclBindingExact Γ (writeHeap σ a c) ↔
      framewiseDeclBindingExact Γ σ := by
  constructor <;> intro h k Γfr σfr hΓ hσfr
  · have hσold : σ.scopes[k]? = some σfr := by
      simpa [writeHeap] using hσfr
    exact h k Γfr σfr hΓ hσold
  · have hσnew : (writeHeap σ a c).scopes[k]? = some σfr := by
      simpa [writeHeap] using hσfr
    exact h k Γfr σfr hΓ hσnew

private theorem assigns_preserves_objectBindingSound_noReady
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    Assigns σ p v σ' → objectBindingSound σ' := by
  intro hσ hassign k x υ a hbind
  rcases hassign with ⟨a0, c0, _, hheap0, halive0, _, rfl⟩
  have hbind_old : runtimeFrameBindsObject σ k x υ a := by
    simpa [runtimeFrameBindsObject, writeHeap] using hbind
  rcases hσ.objectBindingSound hbind_old with ⟨hown, hlive⟩
  refine ⟨by simpa [runtimeFrameOwnsAddress, writeHeap] using hown, ?_⟩
  rcases hlive with ⟨c, hheap, hty, halive⟩
  by_cases ha : a = a0
  · subst ha
    let c_new : Cell := { ty := c0.ty, value := some v, alive := c0.alive }
    refine ⟨c_new, ?_, ?_, halive0⟩
    · simp [writeHeap, c_new]
    · simp [hheap0] at hheap
      rw [← hty, ← hheap]
  · exact ⟨c, by simp [writeHeap, ha, hheap], hty, halive⟩

private theorem assigns_preserves_refBindingSound_noReady
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    Assigns σ p v σ' → refBindingSound σ' := by
  intro hσ hassign k x υ a hbind
  rcases hassign with ⟨a0, c0, _, hheap0, halive0, _, rfl⟩
  have hbind_old : runtimeFrameBindsRef σ k x υ a := by
    simpa [runtimeFrameBindsRef, writeHeap] using hbind
  rcases hσ.refBindingSound hbind_old with ⟨c, hheap, hty, halive⟩
  by_cases ha : a = a0
  · subst ha
    let c_new : Cell := { ty := c0.ty, value := some v, alive := c0.alive }
    refine ⟨c_new, by simp [writeHeap, c_new], ?_, halive0⟩
    simp [hheap0] at hheap
    rw [← hty, ← hheap]
  · exact ⟨c, by simp [writeHeap, ha, hheap], hty, halive⟩

/--
Ready-free assignment preservation.

Unlike `assigns_preserves_scoped_typed_state_concrete`, this theorem does not
ask for `PlaceReadyConcrete` or an external `ValueCompat v τ`.  The only dynamic
semantic payload it consumes is `Assigns` itself.
-/
theorem assigns_preserves_scoped_typed_state_concrete_noReady
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    Assigns σ p v σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  refine
    { frameDepth := by
        simpa [frameDepthAgreement, writeHeap] using hσ.frameDepth
      namesExact := by
        exact (framewiseDeclBindingExact_writeHeap_stateOnly (Γ := Γ) (σ := σ)
          (a := a0) (c := { c0 with value := some v })).2 hσ.namesExact
      shadowing := by
        intro x d hdecl
        rcases hσ.shadowing x d hdecl with ⟨b, hb, hmatch⟩
        exact ⟨b, by simpa [lookupBinding_writeHeap] using hb, hmatch⟩
      objectDeclRealized := by
        intro k x τ hdecl
        rcases hσ.objectDeclRealized hdecl with ⟨addr, hbind, hown, hlive⟩
        refine ⟨addr, ?_, ?_, ?_⟩
        · exact (runtimeFrameBindsObject_writeHeap_iff_stateOnly
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (x := x) (τ := τ) (addr := addr)).2 hbind
        · exact (runtimeFrameOwnsAddress_writeHeap_iff_stateOnly
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (addr := addr)).2 hown
        · exact heapLiveTypedAt_assigns_preserved_stateOnly
            (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
            (p := p) (v := v) (a := addr) (τ := τ)
            ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩ hlive
      refDeclRealized := by
        intro k x τ hdecl
        rcases hσ.refDeclRealized hdecl with ⟨addr, hbind, hlive⟩
        refine ⟨addr, ?_, ?_⟩
        · exact (runtimeFrameBindsRef_writeHeap_iff_stateOnly
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (x := x) (τ := τ) (addr := addr)).2 hbind
        · exact heapLiveTypedAt_assigns_preserved_stateOnly
            (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
            (p := p) (v := v) (a := addr) (τ := τ)
            ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩ hlive
      objectBindingSound :=
        assigns_preserves_objectBindingSound_noReady
          (Γ := Γ) (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
          (p := p) (v := v) hσ
          ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
      refBindingSound :=
        assigns_preserves_refBindingSound_noReady
          (Γ := Γ) (σ := σ) (σ' := writeHeap σ a0 { c0 with value := some v })
          (p := p) (v := v) hσ
          ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
      ownedAddressNamed := by
        intro k addr hown
        exact hσ.ownedAddressNamed <|
          (runtimeFrameOwnsAddress_writeHeap_iff_stateOnly
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (addr := addr)).1 hown
      refsNotOwned := by
        intro k fr x τ addr hk href hmem
        let hown_new : runtimeFrameOwnsAddress (writeHeap σ a0 { c0 with value := some v }) k addr := ⟨fr, hk, hmem⟩
        have hown_old : runtimeFrameOwnsAddress σ k addr :=
          (runtimeFrameOwnsAddress_writeHeap_iff_stateOnly (a := a0) (c := { c0 with value := some v })).1 hown_new
        rcases hown_old with ⟨fr_old, hk_old, hmem_old⟩
        have hfr_eq : fr = fr_old := by
          simp [writeHeap] at hk
          rw [hk] at hk_old
          injection hk_old
        subst hfr_eq
        exact hσ.refsNotOwned k fr x τ addr hk_old href hmem
      objectsOwned := by
        intro k x τ addr hbind
        exact (runtimeFrameOwnsAddress_writeHeap_iff_stateOnly
          (σ := σ) (a := a0) (c := { c0 with value := some v })
          (k := k) (addr := addr)).2 <|
            hσ.objectsOwned k x τ addr <|
              (runtimeFrameBindsObject_writeHeap_iff_stateOnly
                (σ := σ) (a := a0) (c := { c0 with value := some v })
                (k := k) (x := x) (τ := τ) (addr := addr)).1 hbind
      ownedNoDupPerFrame := by
        intro k fr hk
        exact hσ.ownedNoDupPerFrame k fr <|
          by simpa [writeHeap, runtimeFrameOwnsAddress] using hk
      ownedDisjoint := by
        intro i j fi fj addr hij hi hj hai haj
        exact hσ.ownedDisjoint i j fi fj addr hij
          (by simpa [writeHeap] using hi)
          (by simpa [writeHeap] using hj) hai haj
      ownedNamed := by
        intro k addr hown
        have hown_old : runtimeFrameOwnsAddress σ k addr :=
          (runtimeFrameOwnsAddress_writeHeap_iff_stateOnly (a := a0) (c := { c0 with value := some v })).1 hown
        rcases hσ.ownedNamed k addr hown_old with ⟨x, τ_obj, hbind_old⟩
        refine ⟨x, τ_obj, ?_⟩
        exact (runtimeFrameBindsObject_writeHeap_iff_stateOnly (a := a0) (c := { c0 with value := some v })).2 hbind_old
      heapStoredValuesTyped :=
        heapInitializedValuesTyped_after_assigns_stateOnly
          (Γ := Γ) (σ := σ)
          (p := p) (v := v)
          hσ
          ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
      nextFresh := by
        rcases hσ.nextFresh with ⟨hheapNone, hlocals⟩
        refine ⟨?_, ?_⟩
        · have hne : a0 ≠ σ.next := by
            exact assigned_addr_ne_next_stateOnly (Γ := Γ) (σ := σ)
              hσ ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩ hplace hheap0
          simpa [writeHeap, hne, eq_comm] using hheapNone
        · intro k fr hk
          simpa [writeHeap] using hlocals k fr hk
      refTargetsAvoidInnerOwned := by
        intro k x τ addr j href hjk hown
        exact hσ.refTargetsAvoidInnerOwned
          ((runtimeFrameBindsRef_writeHeap_iff_stateOnly
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := k) (x := x) (τ := τ) (addr := addr)).1 href)
          hjk
          ((runtimeFrameOwnsAddress_writeHeap_iff_stateOnly
            (σ := σ) (a := a0) (c := { c0 with value := some v })
            (k := j) (addr := addr)).1 hown) }

end StateOnlyAssign

/-! ## Primitive statement wrappers -/

theorem skip_stmt_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State} :
    HasTypeStmtCI .normalK Γ .skip Δ →
    ScopedTypedStateConcrete Γ σ →
    BigStepStmt σ .skip .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hstep
  cases hty
  cases hstep
  exact hσ

theorem exprStmt_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.exprStmt e) Δ →
    ScopedTypedStateConcrete Γ σ →
    BigStepStmt σ (.exprStmt e) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hstep
  cases hty
  cases hstep
  exact hσ

theorem assign_stmt_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.assign p e) Δ →
    ScopedTypedStateConcrete Γ σ →
    BigStepStmt σ (.assign p e) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hstep
  cases hty with
  | assign hp hv =>
      cases hstep with
      | assign h_bs_val hassign =>
          rename_i v
          exact StateOnlyAssign.assigns_preserves_scoped_typed_state_concrete_noReady
            (Γ := Γ) (σ := σ) (σ' := σ') (p := p) (v := v) hσ hassign

theorem declareObj_stmt_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {oe : Option ValExpr} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x oe) Δ →
    ScopedTypedStateConcrete Γ σ →
    BigStepStmt σ (.declareObj τ x oe) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hstep
  cases hty with
  | declareObjNone hfresh hobj =>
      cases hstep with
      | declareObjNone hdecl =>
          exact declares_object_preserves_scoped_typed_state_concrete hfresh hσ hdecl
  | declareObjSome hfresh hobj hv =>
      cases hstep with
      | declareObjSome h_bs_val hdecl =>
          exact declares_object_preserves_scoped_typed_state_concrete hfresh hσ hdecl

theorem declareRef_stmt_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {p : PlaceExpr} :
    HasTypeStmtCI .normalK Γ (.declareRef τ x p) Δ →
    ScopedTypedStateConcrete Γ σ →
    BigStepStmt σ (.declareRef τ x p) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hstep
  cases hty with
  | declareRef hfresh hp =>
      cases hstep with
      | declareRef h_bs_place hdecl =>
          exact declares_ref_preserves_scoped_typed_state_concrete hfresh hσ hdecl

theorem primitive_stmt_normal_preserves_scoped_typed_state_concrete_noReady
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    (match st with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) →
    HasTypeStmtCI .normalK Γ st Δ →
    ScopedTypedStateConcrete Γ σ →
    BigStepStmt σ st .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hstep
  cases st <;> simp at hprim
  case skip =>
    exact skip_stmt_normal_preserves_scoped_typed_state_concrete_noReady hty hσ hstep
  case exprStmt e =>
    exact exprStmt_normal_preserves_scoped_typed_state_concrete_noReady hty hσ hstep
  case assign p e =>
    exact assign_stmt_normal_preserves_scoped_typed_state_concrete_noReady hty hσ hstep
  case declareObj τ x oe =>
    exact declareObj_stmt_normal_preserves_scoped_typed_state_concrete_noReady hty hσ hstep
  case declareRef τ x p =>
    exact declareRef_stmt_normal_preserves_scoped_typed_state_concrete_noReady hty hσ hstep

end Cpp
