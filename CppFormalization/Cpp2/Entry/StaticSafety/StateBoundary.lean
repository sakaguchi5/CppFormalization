import CppFormalization.Cpp2.Static.SafetyPolicy.Assumptions
import CppFormalization.Cpp2.RuntimeModel.RuntimeQuery
import CppFormalization.Cpp2.RuntimeModel.Facts.RuntimeState
import CppFormalization.Cpp2.RuntimeModel.Facts.RuntimeDeclUpdate

namespace Cpp

/-!
# CppFormalization.Cpp2.Static.Safety.StateBoundary

Runtime-side safety boundary vocabulary.

位置づけ:
- `Static.Safety` は C++ execution が安全に始められるための runtime/state 側条件を置く。
- ここには Closure boundary / adequacy / preservation assembly は置かない。
- old Closure.Foundation path は compatibility wrapper として残す。
-/


/-- 型環境と runtime state の frame 数が一致する。第一近似として長さ一致だけを採用する。 -/
def scopesCompatible (Γ : TypeEnv) (σ : State) : Prop :=
  Γ.scopes.length = σ.scopes.length

/--
各 runtime frame の `locals` は、その frame 内の object binding address とちょうど一致する。
ここでは type-env 側とは直接結び付けず、runtime frame 自体の整合条件として書く。
-/
def frameLocalsExact (_Γ : TypeEnv) (σ : State) : Prop :=
  ∀ (k : Nat) fr,
    σ.scopes[k]? = some fr →
    ∀ a, a ∈ fr.locals ↔ frameBindsObjectAddr fr a

/-- 異なる frame の `locals` は交わらない。 -/
def ownedAddressesDisjoint (σ : State) : Prop :=
  ∀ (i j : Nat) fi fj a,
    i ≠ j →
    σ.scopes[i]? = some fi →
    σ.scopes[j]? = some fj →
    a ∈ fi.locals →
    a ∉ fj.locals

@[simp] theorem ownedAddressesDisjoint_writeHeap
    {σ : State} {a : Nat} {c : Cell} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (writeHeap σ a c) := by
  intro hdisj
  unfold ownedAddressesDisjoint
  change
    ∀ (i j : Nat) fi fj aOwned,
      i ≠ j →
      σ.scopes[i]? = some fi →
      σ.scopes[j]? = some fj →
      aOwned ∈ fi.locals →
      aOwned ∉ fj.locals
  exact hdisj

@[simp] theorem ownedAddressesDisjoint_setNext
    {σ : State} {n : Nat} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint ({ σ with next := n }) := by
  intro hdisj
  unfold ownedAddressesDisjoint
  change
    ∀ (i j : Nat) fi fj aOwned,
      i ≠ j →
      σ.scopes[i]? = some fi →
      σ.scopes[j]? = some fj →
      aOwned ∈ fi.locals →
      aOwned ∉ fj.locals
  exact hdisj

theorem ownedAddressesDisjoint_pushScope
    {σ : State} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (pushScope σ) := by
  intro hdisj
  unfold ownedAddressesDisjoint at *
  intro i j fi fj a hij hi hj hai

  rcases pushScope_scope_locals_empty_or_old hi with hfi_empty | ⟨i₀, fi₀, hi_eq, hi₀, hfi_locals⟩
  · exact False.elim (by simp [hfi_empty] at hai)

  rcases pushScope_scope_locals_empty_or_old hj with hfj_empty | ⟨j₀, fj₀, hj_eq, hj₀, hfj_locals⟩
  · intro haj
    exact (by simp [hfj_empty] at haj)

  · have hij₀ : i₀ ≠ j₀ := by
      intro hij₀
      apply hij
      calc
        i = i₀.succ := hi_eq
        _ = j₀.succ := by simp [hij₀]
        _ = j := hj_eq.symm

    have hai₀ : a ∈ fi₀.locals := by
      simpa [hfi_locals] using hai

    have hnot₀ : a ∉ fj₀.locals :=
      hdisj i₀ j₀ fi₀ fj₀ a hij₀ hi₀ hj₀ hai₀

    intro haj
    exact hnot₀ (by simpa [hfj_locals] using haj)

theorem ownedAddressesDisjoint_bindTopBinding
    {σ : State} {x : Ident} {b : Binding} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (bindTopBinding σ x b) := by
  intro hdisj
  unfold ownedAddressesDisjoint at *
  intro i j fi fj a hij hi hj hai

  rcases bindTopBinding_scope_locals_empty_or_old hi with hfi_empty | ⟨fi₀, hi₀, hfi_locals⟩
  · exact False.elim (by simp [hfi_empty] at hai)

  rcases bindTopBinding_scope_locals_empty_or_old hj with hfj_empty | ⟨fj₀, hj₀, hfj_locals⟩
  · intro haj
    exact (by simp [hfj_empty] at haj)

  · have hai₀ : a ∈ fi₀.locals := by
      simpa [hfi_locals] using hai
    have hnot₀ : a ∉ fj₀.locals :=
      hdisj i j fi₀ fj₀ a hij hi₀ hj₀ hai₀
    intro haj
    exact hnot₀ (by simpa [hfj_locals] using haj)

@[simp] theorem ownedAddressesDisjoint_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (declareRefState σ τ x a) := by
  intro hdisj
  unfold declareRefState
  exact ownedAddressesDisjoint_bindTopBinding (σ := σ) (x := x) (b := .ref τ a) hdisj

/-- heap に入っている initialized value は cell の型に整合する。 -/
def heapInitializedValuesTyped (σ : State) : Prop :=
  ∀ a c v,
    σ.heap a = some c →
    c.value = some v →
    ValueCompat v c.ty

/-- `next` は未使用で、どの frame の `locals` にも現れない。 -/
def nextIsFreshForOwnedHeap (σ : State) : Prop :=
  σ.heap σ.next = none ∧
  ∀ (k : Nat) fr,
    σ.scopes[k]? = some fr →
    σ.next ∉ fr.locals

theorem nextIsFreshForOwnedHeap_bindTopBinding
    {σ : State} {x : Ident} {b : Binding} :
    nextIsFreshForOwnedHeap σ →
    nextIsFreshForOwnedHeap (bindTopBinding σ x b) := by
  intro h
  rcases h with ⟨hheap, hfresh⟩
  refine ⟨?_, ?_⟩
  · simpa using hheap
  · intro k fr hk
    rcases bindTopBinding_scope_locals_empty_or_old hk with hfr_empty | ⟨fr₀, hk₀, hfr_locals⟩
    · intro hmem
      exact (by simp [hfr_empty] at hmem)
    · simpa [hfr_locals] using hfresh k fr₀ hk₀

@[simp] theorem nextIsFreshForOwnedHeap_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    nextIsFreshForOwnedHeap σ →
    nextIsFreshForOwnedHeap (declareRefState σ τ x a) := by
  intro h
  unfold declareRefState
  exact nextIsFreshForOwnedHeap_bindTopBinding (x := x) (b := .ref τ a) h

@[simp] theorem nextIsFreshForOwnedHeap_pushScope
    {σ : State} :
    nextIsFreshForOwnedHeap σ →
    nextIsFreshForOwnedHeap (pushScope σ) := by
  intro h
  rcases h with ⟨hheap, hfresh⟩
  refine ⟨?_, ?_⟩
  · change σ.heap σ.next = none
    exact hheap
  · intro k fr hk
    change σ.next ∉ fr.locals
    rcases pushScope_scope_locals_empty_or_old hk with hfr_empty | ⟨k₀, fr₀, _, hk₀, hfr_locals⟩
    · intro hmem
      rw [hfr_empty] at hmem
      cases hmem
    · rw [hfr_locals]
      exact hfresh k₀ fr₀ hk₀


/-- `PlaceReady Γ σ p τ` は、`p` が現在の状態で安全に使える `τ`-place であること。 -/
def PlaceReady (Γ : TypeEnv) (σ : State) (p : PlaceExpr) (τ : CppType) : Prop :=
  HasPlaceType Γ p τ ∧
  NoInvalidRefPlace σ p

/-- `ExprReady Γ σ e τ` は、`e` が現在の状態で安全に評価できる `τ`-expr であること。 -/
def ExprReady (Γ : TypeEnv) (σ : State) (e : ValExpr) (τ : CppType) : Prop :=
  HasValueType Γ e τ ∧
  NoUninitValue σ e ∧
  NoInvalidRefValue σ e

/-- statement / block 開始時の安全準備条件。 -/
def StmtReady (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  WellTypedFrom Γ st ∧
  NoUninitStmt σ st ∧
  NoInvalidRefStmt σ st

def BlockReady (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop :=
  (∃ Δ, HasTypeBlock Γ ss Δ) ∧
  NoUninitBlock σ ss ∧
  NoInvalidRefBlock σ ss


/-- 1 個の type frame と 1 個の runtime frame の対応。 -/
def frameDeclBindingCompatibleAt (Γfr : TypeFrame) (σfr : ScopeFrame) : Prop :=
  ∀ x d,
    Γfr.decls x = some d →
    ∃ b, σfr.binds x = some b ∧ DeclMatchesBinding d b

/--
各深さの type frame / runtime frame が局所的に整合している。
ここでは shadowing 後の global lookup ではなく、frame ごとの対応を coarse に取る。
-/
def framewiseDeclBindingCompatible (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ (k : Nat) Γfr σfr,
    Γ.scopes[k]? = some Γfr →
    σ.scopes[k]? = some σfr →
    frameDeclBindingCompatibleAt Γfr σfr

/-- 1 個の object decl が、その frame の object binding / live cell / owned local に実現される。 -/
def objectDeclBindingLiveTypedOwnedAt
    (Γfr : TypeFrame) (σfr : ScopeFrame) (heap : Nat → Option Cell) : Prop :=
  ∀ x τ,
    Γfr.decls x = some (.object τ) →
    ∃ a c,
      σfr.binds x = some (.object τ a) ∧
      heap a = some c ∧
      c.ty = τ ∧
      c.alive = true ∧
      a ∈ σfr.locals

/--
各深さの object decl は、その frame 内の object binding と
heap 上の live typed cell と local ownership に実現される。
-/
def objectBindingsLiveTypedOwned (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ (k : Nat) Γfr σfr,
    Γ.scopes[k]? = some Γfr →
    σ.scopes[k]? = some σfr →
    objectDeclBindingLiveTypedOwnedAt Γfr σfr σ.heap

/-- 1 個の ref decl が、その frame の ref binding と live typed target に実現される。 -/
def refDeclBindingLiveTypedAt
    (Γfr : TypeFrame) (σfr : ScopeFrame) (heap : Nat → Option Cell) : Prop :=
  ∀ x τ,
    Γfr.decls x = some (.ref τ) →
    ∃ a c,
      σfr.binds x = some (.ref τ a) ∧
      heap a = some c ∧
      c.ty = τ ∧
      c.alive = true

/--
各深さの ref decl は、その frame 内の ref binding と
heap 上の live typed target に実現される。
object と違って ownership は要求しない。
-/
def refBindingsLiveTyped (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ (k : Nat) Γfr σfr,
    Γ.scopes[k]? = some Γfr →
    σ.scopes[k]? = some σfr →
    refDeclBindingLiveTypedAt Γfr σfr σ.heap

/-- `TypedState` より強い runtime invariant. -/
structure ScopedTypedState (Γ : TypeEnv) (σ : State) : Prop where
  stackAligned : scopesCompatible Γ σ
  frameDeclBinding : framewiseDeclBindingCompatible Γ σ
  objectBindingsSound : objectBindingsLiveTypedOwned Γ σ
  refBindingsSound : refBindingsLiveTyped Γ σ
  localsExact : frameLocalsExact Γ σ
  ownedDisjoint : ownedAddressesDisjoint σ
  initializedValuesTyped : heapInitializedValuesTyped σ
  nextFresh : nextIsFreshForOwnedHeap σ

/-- coarse compatibility façade retained for old-to-new bridges. -/
structure BodyReady (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  typed : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st
  state : ScopedTypedState Γ σ
  safe : StmtReady Γ σ st

end Cpp
