import CppFormalization.Cpp2.Static.Assumptions
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Closure.Foundation.StateBoundaryNoAxioms

namespace Cpp

/-!
# Closure.Foundation.StateBoundary

Compatibility substrate for coarse runtime-side boundary vocabulary.

位置づけ:
- mainline closure theorem の入口はもはや四層 assembled boundary (`BodyClosureBoundaryCI`) である。
- それでも concrete readiness や一部の old coarse compatibility theorem が参照する
  runtime / readiness facade は依然として必要なので、ここに canonical に残す。
- 以前の `Closure.Legacy.*` に退避していた内容をここへ戻し、
  `Legacy` 名前空間依存を除去する。
-/

axiom framewiseDeclBindingCompatible : TypeEnv → State → Prop
axiom objectBindingsLiveTypedOwned : TypeEnv → State → Prop
axiom refBindingsLiveTyped : TypeEnv → State → Prop

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
