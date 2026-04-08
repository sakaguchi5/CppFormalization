import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteReadyTransport

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteOwnershipAssembly

`StateInvariantConcreteReadyTransport` で準備した transport 定理を
`ScopedTypedStateConcreteOwnership` の bundle へ束ねる層。

今回の責務:
- ref declaration 側の full ownership bundle を完成させる。
- object declaration 側では、残っていた frame 間 disjointness をここで証明し、
  fresh successor 仮定のもとで full ownership bundle を完成させる。
-/

namespace DeclareObjectReadyStrong

/--
object 宣言後も frame 間 ownership disjointness は保存される。

考え方:
- deeper frames (`k.succ`) は locals が不変。
- top frame (`0`) だけが `σ.next :: fr0.locals` に変わる。
- したがって新しい衝突候補は `σ.next` だけだが、これは `nextFreshAgainstOwned σ`
  によりどの旧 frame locals にも属さない。
- それ以外の address は旧 top frame と deeper frame の disjointness へ戻る。
-/
theorem ownedDisjoint_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {τ : CppType} {ov : Option Value} :
    ownedAddressesDisjointAcrossFrames (declareObjectState σ τ x ov) := by
  rcases h.concrete.nextFresh with ⟨_, hfreshLocals⟩
  intro i j fi fj addr hij hi hj hai
  intro haj
  cases hsc : σ.scopes with
  | nil =>
      cases i with
      | zero =>
          cases j with
          | zero => exact (hij rfl).elim
          | succ j =>
              simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc] at hj
      | succ i =>
          simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc] at hi
  | cons fr0 frs =>
      cases i with
      | zero =>
          cases j with
          | zero =>
              exact (hij rfl).elim
          | succ j =>
              have hfiLocals : fi.locals = σ.next :: fr0.locals := by
                exact declareObjectState_lookup_zero_locals_of_cons
                  (σ := σ) (τ := τ) (x := x) (ov := ov)
                  (fr0 := fr0) (frs := frs) hsc hi
              have hjOld : σ.scopes[j.succ]? = some fj := by
                exact (declareObjectState_lookup_succ_iff
                  (σ := σ) (τ := τ) (x := x) (ov := ov)
                  (k := j) (fr := fj)).1 hj
              by_cases hEq : addr = σ.next
              · subst addr
                exact hfreshLocals j.succ fj hjOld haj
              · have haiOld : addr ∈ fr0.locals := by
                  simpa [hfiLocals, hEq] using hai
                exact (h.concrete.ownedDisjoint 0 j.succ fr0 fj addr
                  (by simp) (by simp [hsc]) hjOld haiOld) haj
      | succ i =>
          cases j with
          | zero =>
              have hiOld : σ.scopes[i.succ]? = some fi := by
                exact (declareObjectState_lookup_succ_iff
                  (σ := σ) (τ := τ) (x := x) (ov := ov)
                  (k := i) (fr := fi)).1 hi
              have hfjLocals : fj.locals = σ.next :: fr0.locals := by
                exact declareObjectState_lookup_zero_locals_of_cons
                  (σ := σ) (τ := τ) (x := x) (ov := ov)
                  (fr0 := fr0) (frs := frs) hsc hj
              by_cases hEq : addr = σ.next
              · subst addr
                exact hfreshLocals i.succ fi hiOld hai
              · have hajOld : addr ∈ fr0.locals := by
                  simpa [hfjLocals, hEq] using haj
                exact (h.concrete.ownedDisjoint i.succ 0 fi fr0 addr
                  (by simp) hiOld (by simp [hsc]) hai) hajOld
          | succ j =>
              have hiOld : σ.scopes[i.succ]? = some fi := by
                exact (declareObjectState_lookup_succ_iff
                  (σ := σ) (τ := τ) (x := x) (ov := ov)
                  (k := i) (fr := fi)).1 hi
              have hjOld : σ.scopes[j.succ]? = some fj := by
                exact (declareObjectState_lookup_succ_iff
                  (σ := σ) (τ := τ) (x := x) (ov := ov)
                  (k := j) (fr := fj)).1 hj
              exact (h.concrete.ownedDisjoint i.succ j.succ fi fj addr
                (by simpa using hij) hiOld hjOld hai) haj

/-- object 宣言後の ownership bundle。 -/
theorem ownership_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value}
    (hnextSucc : freshAddrAgainstOwned σ (σ.next + 1)) :
    ScopedTypedStateConcreteOwnership (declareObjectState σ τ x ov) := by
  refine
    { ownedAddressNamed :=
        @ownedNamed_after_declareObjectState Γ σ x h Γfr hΓ0 τ ov
      refsNotOwned :=
        refsNotOwned_after_declareObjectState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov)
      objectsOwned :=
        objectsOwned_after_declareObjectState
          (h := h) (τ := τ) (ov := ov)
      ownedNoDupPerFrame :=
        ownedNoDup_after_declareObjectState
          (h := h) (τ := τ) (ov := ov)
      ownedDisjoint :=
        ownedDisjoint_after_declareObjectState
          (h := h) (τ := τ) (ov := ov)
      ownedNamed :=
        ownedNamed_after_declareObjectState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov)
      nextFresh :=
        nextFresh_after_declareObjectState
         (τ := τ) (ov := ov) hnextSucc
      refTargetsAvoidInnerOwned :=
        refTargetsAvoidInnerOwned_after_declareObjectState
          (h := h) (τ := τ) (ov := ov) }

end DeclareObjectReadyStrong

namespace DeclareRefReadyStrong

/-- ref 宣言後の ownership bundle。 -/
theorem ownership_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat} :
    ScopedTypedStateConcreteOwnership (declareRefState σ τ x a) := by
  refine
    { ownedAddressNamed :=
        @ownedNamed_after_declareRefState Γ σ x h Γfr hΓ0 τ a
      refsNotOwned :=
        refsNotOwned_after_declareRefState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a)
      objectsOwned :=
        objectsOwned_after_declareRefState
          (h := h) (τ := τ) (a := a)
      ownedNoDupPerFrame :=
        ownedNoDup_after_declareRefState
          (h := h) (τ := τ) (a := a)
      ownedDisjoint :=
        ownedDisjoint_after_declareRefState
          (h := h) (τ := τ) (a := a)
      ownedNamed :=
        ownedNamed_after_declareRefState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a)
      nextFresh :=
        nextFresh_after_declareRefState
          (h := h) (τ := τ) (a := a)
      refTargetsAvoidInnerOwned :=
        refTargetsAvoidInnerOwned_after_declareRefState
          (h := h) (τ := τ) (a := a) }

end DeclareRefReadyStrong

end Cpp
