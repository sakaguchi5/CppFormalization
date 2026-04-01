import CppFormalization.Cpp2.Static.Assumptions

namespace Cpp

/-!
# Closure.Foundation.StateBoundary

Closure theorem へ向かうための「状態境界」と「開始準備条件」の層。

意図:
- 旧 `IdealAssumptions` を、そのまま closure の前提にしない。
- runtime invariant と statement-local safety を分ける。
- 既存 Core の theorem を壊さず、その上に乗る新しい境界語彙を用意する。
-/

axiom scopesCompatible : TypeEnv → State → Prop
axiom framewiseDeclBindingCompatible : TypeEnv → State → Prop
axiom objectBindingsLiveTypedOwned : TypeEnv → State → Prop
axiom refBindingsLiveTyped : TypeEnv → State → Prop
axiom frameLocalsExact : TypeEnv → State → Prop
axiom ownedAddressesDisjoint : State → Prop
axiom heapInitializedValuesTyped : State → Prop
axiom nextIsFreshForOwnedHeap : State → Prop

/--
`TypedState` より強い runtime invariant.
核心は scope stack 対応と ownership discipline.
-/
structure ScopedTypedState (Γ : TypeEnv) (σ : State) : Prop where
  stackAligned : scopesCompatible Γ σ
  frameDeclBinding : framewiseDeclBindingCompatible Γ σ
  objectBindingsSound : objectBindingsLiveTypedOwned Γ σ
  refBindingsSound : refBindingsLiveTyped Γ σ
  localsExact : frameLocalsExact Γ σ
  ownedDisjoint : ownedAddressesDisjoint σ
  initializedValuesTyped : heapInitializedValuesTyped σ
  nextFresh : nextIsFreshForOwnedHeap σ


def PlaceReady (Γ : TypeEnv) (σ : State) (p : PlaceExpr) (τ : CppType) : Prop :=
  HasPlaceType Γ p τ ∧
  NoInvalidRefPlace σ p

def ExprReady (Γ : TypeEnv) (σ : State) (e : ValExpr) (τ : CppType) : Prop :=
  HasValueType Γ e τ ∧
  NoUninitValue σ e ∧
  NoInvalidRefValue σ e

def StmtReady (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  WellTypedFrom Γ st ∧
  NoUninitStmt σ st ∧
  NoInvalidRefStmt σ st

def BlockReady (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop :=
  (∃ Δ, HasTypeBlock Γ ss Δ) ∧
  NoUninitBlock σ ss ∧
  NoInvalidRefBlock σ ss

/--
closure theorem の本当の前提。
旧 `IdealAssumptions` をそのまま使わず、必要な層を明示的に分解する。
-/
structure BodyReady (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  typed : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st
  state : ScopedTypedState Γ σ
  safe : StmtReady Γ σ st

theorem bodyReady_of_idealAssumptions
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : IdealAssumptions Γ σ st)
    (hstate : ScopedTypedState Γ σ) :
    BodyReady Γ σ st := by
  rcases h with ⟨hwf, htyped, htypedState, hnu, hnir, hbreak, hcont⟩
  exact
    { wf := hwf
      typed := htyped
      breakScoped := hbreak
      continueScoped := hcont
      state := hstate
      safe := ⟨htyped, hnu, hnir⟩ }

end Cpp
