import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteFullAssembly

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteRecomputedCursor

`σ.next + 1` を post-state cursor に固定する代わりに、
object 本体を書き込んだ後で「次に使ってよい cursor」を別 witness として与える層。

この段階では、まだ core の `declareObjectState` を直接置き換えない。
代わりに:
- object 本体を書き込む core update (`declareObjectStateCore`)
- post-state cursor witness (`RecomputedNextWitness`)
- その witness を使った recomputed state (`declareObjectStateRecomputed`)

を切り出し、`hnextSucc : freshAddrAgainstOwned σ (σ.next + 1)` を
後で除去するための接着 API を先に用意する。
-/

/--
`declareObjectState` から post-state cursor 更新だけを外した core update.

- 新 object の address は従来どおり pre-state の `σ.next`
- binding / heap / top-local recording までは従来どおり
- post-state の `next` だけはまだ更新しない
-/
def declareObjectStateCore (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) : State :=
  let a := σ.next
  let σ1 := bindTopBinding σ x (.object τ a)
  let σ2 := writeHeap σ1 a { ty := τ, value := ov, alive := true }
  recordLocal σ2 a

/--
post-state cursor として採用してよい address witness.

要求するのは次の四つ:
- monotone: pre-state cursor より後退しない
- heapFresh: heap 上で未使用
- notOwned: どの frame locals にも載っていない
- notRefTarget: どの runtime ref binding の target にもなっていない
-/
structure RecomputedNextWitness (σ : State) : Type where
  addr : Nat
  freshOwned : freshAddrAgainstOwned σ addr
  notRuntimeRefTarget :
    ∀ {k : Nat} {x : Ident} {τ : CppType},
      ¬ runtimeFrameBindsRef σ k x τ addr
  monotone : σ.next ≤ addr

/--
`declareObjectStateCore` の後で、cursor だけ recompute witness に差し替えた state.
-/
def declareObjectStateRecomputed
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) : State :=
  { declareObjectStateCore σ τ x ov with next := w.addr }

namespace RecomputedNextWitness

@[simp] theorem addr_nonneg
    {σ : State} (w : RecomputedNextWitness σ) :
    0 ≤ w.addr := by
  exact Nat.zero_le _

end RecomputedNextWitness

section CoreStateLemmas

@[simp] theorem next_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).next = σ.next := by
  unfold declareObjectStateCore
  simp

@[simp] theorem scopes_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes = (declareObjectState σ τ x ov).scopes := by
  unfold declareObjectStateCore declareObjectState
  simp [scopes_recordLocal, scopes_writeHeap, scopes_bindTopBinding]

@[simp] theorem heap_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap = (declareObjectState σ τ x ov).heap := by
  unfold declareObjectStateCore declareObjectState
  simp [writeHeap, bindTopBinding]

@[simp] theorem declareObjectStateCore_scopes_ne_nil
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes ≠ [] := by
  rw [scopes_declareObjectStateCore]
  exact declareObjectState_scopes_ne_nil σ τ x ov

@[simp] theorem heap_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  rw [heap_declareObjectStateCore]
  exact declareObjectState_heap_self σ τ x ov

@[simp] theorem heap_declareObjectStateCore_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    {a : Nat} (ha : a ≠ σ.next) :
    (declareObjectStateCore σ τ x ov).heap a = σ.heap a := by
  rw [heap_declareObjectStateCore]
  exact declareObjectState_heap_other σ τ x ov ha

@[simp] theorem declareObjectStateCore_top_local_mem
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    match (declareObjectStateCore σ τ x ov).scopes with
    | [] => False
    | fr :: _ => σ.next ∈ fr.locals := by
  rw [scopes_declareObjectStateCore]
  exact declareObjectState_top_local_mem σ τ x ov

@[simp] theorem lookupBinding_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    lookupBinding (declareObjectStateCore σ τ x ov) x = some (.object τ σ.next) := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateCore σ τ x ov)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateCore σ τ x ov)
      (x := x)
  calc
    lookupBinding (declareObjectStateCore σ τ x ov) x
        = lookupBinding (declareObjectState σ τ x ov) x := hEq
    _ = some (.object τ σ.next) := by simp

@[simp] theorem lookupBinding_declareObjectStateCore_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (hxy : y ≠ x) :
    lookupBinding (declareObjectStateCore σ τ x ov) y = lookupBinding σ y := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateCore σ τ x ov)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateCore σ τ x ov)
      (x := y)
  calc
    lookupBinding (declareObjectStateCore σ τ x ov) y
        = lookupBinding (declareObjectState σ τ x ov) y := hEq
    _ = lookupBinding σ y := by
          simpa using lookupBinding_declareObjectState_other σ τ x y ov hxy

end CoreStateLemmas

section RecomputedStateLemmas

@[simp] theorem scopes_declareObjectStateRecomputed
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    (declareObjectStateRecomputed σ τ x ov w).scopes =
      (declareObjectStateCore σ τ x ov).scopes := by
  unfold declareObjectStateRecomputed
  rfl

@[simp] theorem heap_declareObjectStateRecomputed
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    (declareObjectStateRecomputed σ τ x ov w).heap =
      (declareObjectStateCore σ τ x ov).heap := by
  unfold declareObjectStateRecomputed
  rfl

@[simp] theorem next_declareObjectStateRecomputed
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    (declareObjectStateRecomputed σ τ x ov w).next = w.addr := by
  unfold declareObjectStateRecomputed
  rfl

@[simp] theorem scopes_declareObjectStateRecomputed_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    (declareObjectStateRecomputed σ τ x ov w).scopes =
      (declareObjectState σ τ x ov).scopes := by
  rw [scopes_declareObjectStateRecomputed]
  exact scopes_declareObjectStateCore σ τ x ov

@[simp] theorem heap_declareObjectStateRecomputed_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    (declareObjectStateRecomputed σ τ x ov w).heap =
      (declareObjectState σ τ x ov).heap := by
  rw [heap_declareObjectStateRecomputed]
  exact heap_declareObjectStateCore σ τ x ov

@[simp] theorem lookupBinding_declareObjectStateRecomputed_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    lookupBinding (declareObjectStateRecomputed σ τ x ov w) x = some (.object τ σ.next) := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateRecomputed σ τ x ov w)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateRecomputed_eq_old σ τ x ov w)
      (x := x)
  calc
    lookupBinding (declareObjectStateRecomputed σ τ x ov w) x
        = lookupBinding (declareObjectState σ τ x ov) x := hEq
    _ = some (.object τ σ.next) := by simp

@[simp] theorem lookupBinding_declareObjectStateRecomputed_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov))
    (hxy : y ≠ x) :
    lookupBinding (declareObjectStateRecomputed σ τ x ov w) y = lookupBinding σ y := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateRecomputed σ τ x ov w)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateRecomputed_eq_old σ τ x ov w)
      (x := y)
  calc
    lookupBinding (declareObjectStateRecomputed σ τ x ov w) y
        = lookupBinding (declareObjectState σ τ x ov) y := hEq
    _ = lookupBinding σ y := by
          simpa using lookupBinding_declareObjectState_other σ τ x y ov hxy

/-- recomputed cursor の witness から、そのまま post-state `nextFreshAgainstOwned` が出る。 -/
theorem nextFreshAgainstOwned_of_recomputedCursor
    {σ : State} (w : RecomputedNextWitness σ) :
    nextFreshAgainstOwned { σ with next := w.addr } := by
  exact w.freshOwned

/-- object core state に witness を与えた版。 -/
theorem nextFreshAgainstOwned_declareObjectStateRecomputed
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    nextFreshAgainstOwned (declareObjectStateRecomputed σ τ x ov w) := by
  simpa [declareObjectStateRecomputed] using
    (nextFreshAgainstOwned_of_recomputedCursor
      (σ := declareObjectStateCore σ τ x ov) w)

/-- recomputed cursor はどの runtime ref binding の target にもならない。 -/
theorem recomputedCursor_notRuntimeRefTarget
    {σ : State} (w : RecomputedNextWitness σ) :
    ∀ {k : Nat} {x : Ident} {τ : CppType},
      ¬ runtimeFrameBindsRef { σ with next := w.addr } k x τ w.addr := by
  intro k x τ href
  exact w.notRuntimeRefTarget href

/-- object recomputed state の `next` は ref target と衝突しない。 -/
theorem next_notRuntimeRefTarget_declareObjectStateRecomputed
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (w : RecomputedNextWitness (declareObjectStateCore σ τ x ov)) :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef
          (declareObjectStateRecomputed σ τ x ov w)
          k y υ
          (declareObjectStateRecomputed σ τ x ov w).next := by
  intro k y υ href
  have : ¬ runtimeFrameBindsRef
      { declareObjectStateCore σ τ x ov with next := w.addr } k y υ w.addr :=
    recomputedCursor_notRuntimeRefTarget
      (σ := declareObjectStateCore σ τ x ov) w
  exact this (by simpa [declareObjectStateRecomputed] using href)

end RecomputedStateLemmas

/--
`DeclareObjectReadyStrong` に、post-core cursor witness と initializer 互換性を足した package.

ここではまだ `declareObjectState` 本体を書き換えない。
次段階で、existing full assembly から `hnextSucc` を除くための入口だけを作る。
-/
structure DeclareObjectReadyRecomputed
    (Γ : TypeEnv) (σ : State) (x : Ident) (τ : CppType) (ov : Option Value) : Type where
  base   : DeclareObjectReadyStrong Γ σ x
  cursor : RecomputedNextWitness (declareObjectStateCore σ τ x ov)

namespace DeclareObjectReadyRecomputed

@[simp] theorem nextFresh_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    nextFreshAgainstOwned (declareObjectStateRecomputed σ τ x ov h.cursor) := by
  exact nextFreshAgainstOwned_declareObjectStateRecomputed h.cursor

@[simp] theorem next_not_ref_target_after
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    ∀ {k : Nat} {y : Ident} {υ : CppType},
      ¬ runtimeFrameBindsRef
          (declareObjectStateRecomputed σ τ x ov h.cursor)
          k y υ
          (declareObjectStateRecomputed σ τ x ov h.cursor).next := by
  exact next_notRuntimeRefTarget_declareObjectStateRecomputed h.cursor

@[simp] theorem monotone_next
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov) :
    (declareObjectStateCore σ τ x ov).next ≤
      (declareObjectStateRecomputed σ τ x ov h.cursor).next := by
  simpa [next_declareObjectStateCore, next_declareObjectStateRecomputed] using h.cursor.monotone

end DeclareObjectReadyRecomputed

end Cpp
