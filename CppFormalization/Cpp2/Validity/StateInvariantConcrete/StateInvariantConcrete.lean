import CppFormalization.Cpp2.Static.Env.TypeEnvQuery
import CppFormalization.Cpp2.Validity.RuntimeAgreement.DeclRuntimeMatch
import CppFormalization.Cpp2.RuntimeModel.RuntimeQuery
import CppFormalization.Cpp2.RuntimeModel.RuntimeCell
import CppFormalization.Cpp2.RuntimeModel.RuntimeFreshness
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.HeapTyping

/-!
# CppFormalization.Cpp2.Static.Safety.StateInvariantConcrete

Concrete runtime-state invariant vocabulary.

This file contains the base predicates and bundles saying that a runtime
`State` concretely realizes a `TypeEnv`.

It is intentionally below Closure:
- Closure may consume these invariants through dynamic boundaries and
  preservation routes.
- The invariant vocabulary itself is a static/runtime safety layer, not a
  closure-proof assembly layer.
-/

namespace Cpp

def shadowingCompatible (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ x d, lookupDecl Γ x = some d → ∃ b, lookupBinding σ x = some b ∧ DeclMatchesBinding d b

def frameDepthAgreement (Γ : TypeEnv) (σ : State) : Prop :=
  Γ.scopes.length = σ.scopes.length

/--
1 個の type frame と 1 個の runtime frame が、名前集合について双方向に一致する。

forward:
- type decl があれば matching runtime binding がある

backward:
- runtime binding があれば matching type decl がある
-/
def frameDeclBindingExactAt (Γfr : TypeFrame) (σfr : ScopeFrame) : Prop :=
  (∀ x d,
      Γfr.decls x = some d →
      ∃ b, σfr.binds x = some b ∧ DeclMatchesBinding d b) ∧
  (∀ x b,
      σfr.binds x = some b →
      ∃ d, Γfr.decls x = some d ∧ DeclMatchesBinding d b)

/-- 各深さで frame-local exactness が成り立つ。 -/
def framewiseDeclBindingExact (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ (k : Nat) Γfr σfr,
    Γ.scopes[k]? = some Γfr →
    σ.scopes[k]? = some σfr →
    frameDeclBindingExactAt Γfr σfr

def ownedAddressesNoDupPerFrame (σ : State) : Prop :=
  ∀ (k : Nat) (fr : ScopeFrame), σ.scopes[k]? = some fr → fr.locals.Nodup

def ownedAddressesDisjointAcrossFrames (σ : State) : Prop :=
  ∀ (i j : Nat) fi fj a, i ≠ j → σ.scopes[i]? = some fi → σ.scopes[j]? = some fj → a ∈ fi.locals → a ∉ fj.locals

def allObjectBindingsOwned (σ : State) : Prop :=
  ∀ k x τ a, runtimeFrameBindsObject σ k x τ a → runtimeFrameOwnsAddress σ k a

def allOwnedAddressesNamed (σ : State) : Prop :=
  ∀ k a, runtimeFrameOwnsAddress σ k a → ∃ x τ, runtimeFrameBindsObject σ k x τ a

def objectBindingSound (σ : State) : Prop :=
  ∀ {k x τ a}, runtimeFrameBindsObject σ k x τ a → runtimeFrameOwnsAddress σ k a ∧ heapLiveTypedAt σ a τ

def refBindingSound (σ : State) : Prop :=
  ∀ {k x τ a}, runtimeFrameBindsRef σ k x τ a → heapLiveTypedAt σ a τ


def refBindingsNeverOwned (σ : State) : Prop :=
  ∀ (k : Nat) (fr : ScopeFrame) (x : Ident) (τ : CppType) (a : Nat),
    σ.scopes[k]? = some fr → fr.binds x = some (.ref τ a) → a ∈ fr.locals → ∃ y υ, fr.binds y = some (.object υ a)

structure ScopedTypedStateConcreteKernel (Γ : TypeEnv) (σ : State) : Prop where
  frameDepth : frameDepthAgreement Γ σ
  namesExact : framewiseDeclBindingExact Γ σ
  shadowing : shadowingCompatible Γ σ
  objectDeclRealized : ∀ {k x τ}, typeFrameDeclObject Γ k x τ → ∃ a, runtimeFrameBindsObject σ k x τ a ∧ runtimeFrameOwnsAddress σ k a ∧ heapLiveTypedAt σ a τ
  refDeclRealized : ∀ {k x τ}, typeFrameDeclRef Γ k x τ → ∃ a, runtimeFrameBindsRef σ k x τ a ∧ heapLiveTypedAt σ a τ
  objectBindingSound : objectBindingSound σ
  refBindingSound : refBindingSound σ

structure ScopedTypedStateConcreteOwnership (σ : State) : Prop where
  ownedAddressNamed : ∀ {k a}, runtimeFrameOwnsAddress σ k a → ∃ x τ, runtimeFrameBindsObject σ k x τ a
  refsNotOwned : refBindingsNeverOwned σ
  objectsOwned : allObjectBindingsOwned σ
  ownedNoDupPerFrame : ownedAddressesNoDupPerFrame σ
  ownedDisjoint : ownedAddressesDisjointAcrossFrames σ
  ownedNamed : allOwnedAddressesNamed σ
  nextFresh : nextFreshAgainstOwned σ
  refTargetsAvoidInnerOwned : ∀ {k x τ a j}, runtimeFrameBindsRef σ k x τ a → j < k → ¬ runtimeFrameOwnsAddress σ j a

structure ScopedTypedStateConcrete (Γ : TypeEnv) (σ : State) : Prop where
  frameDepth : frameDepthAgreement Γ σ
  namesExact : framewiseDeclBindingExact Γ σ
  shadowing : shadowingCompatible Γ σ
  objectDeclRealized : ∀ {k x τ}, typeFrameDeclObject Γ k x τ → ∃ a, runtimeFrameBindsObject σ k x τ a ∧ runtimeFrameOwnsAddress σ k a ∧ heapLiveTypedAt σ a τ
  refDeclRealized : ∀ {k x τ}, typeFrameDeclRef Γ k x τ → ∃ a, runtimeFrameBindsRef σ k x τ a ∧ heapLiveTypedAt σ a τ
  objectBindingSound : objectBindingSound σ
  refBindingSound : refBindingSound σ
  ownedAddressNamed : ∀ {k a}, runtimeFrameOwnsAddress σ k a → ∃ x τ, runtimeFrameBindsObject σ k x τ a
  refsNotOwned : refBindingsNeverOwned σ
  objectsOwned : allObjectBindingsOwned σ
  ownedNoDupPerFrame : ownedAddressesNoDupPerFrame σ
  ownedDisjoint : ownedAddressesDisjointAcrossFrames σ
  ownedNamed : allOwnedAddressesNamed σ
  heapStoredValuesTyped : heapInitializedValuesTyped σ
  nextFresh : nextFreshAgainstOwned σ
  refTargetsAvoidInnerOwned : ∀ {k x τ a j}, runtimeFrameBindsRef σ k x τ a → j < k → ¬ runtimeFrameOwnsAddress σ j a

namespace ScopedTypedStateConcrete

def kernel {Γ : TypeEnv} {σ : State} (h : ScopedTypedStateConcrete Γ σ) : ScopedTypedStateConcreteKernel Γ σ :=
  { frameDepth := h.frameDepth
    namesExact := h.namesExact
    shadowing := h.shadowing
    objectDeclRealized := h.objectDeclRealized
    refDeclRealized := h.refDeclRealized
    objectBindingSound := h.objectBindingSound
    refBindingSound := h.refBindingSound }

def ownership {Γ : TypeEnv} {σ : State} (h : ScopedTypedStateConcrete Γ σ) : ScopedTypedStateConcreteOwnership σ :=
  { ownedAddressNamed := h.ownedAddressNamed
    refsNotOwned := h.refsNotOwned
    objectsOwned := h.objectsOwned
    ownedNoDupPerFrame := h.ownedNoDupPerFrame
    ownedDisjoint := h.ownedDisjoint
    ownedNamed := h.ownedNamed
    nextFresh := h.nextFresh
    refTargetsAvoidInnerOwned := h.refTargetsAvoidInnerOwned }

def initStrong {Γ : TypeEnv} {σ : State} (h : ScopedTypedStateConcrete Γ σ) : heapInitializedValuesTyped σ := h.heapStoredValuesTyped

end ScopedTypedStateConcrete
end Cpp
