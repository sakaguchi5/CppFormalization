import CppFormalization.Cpp2.Static.Assumptions
import CppFormalization.Cpp2.Semantics.Stmt
import CppFormalization.Cpp2.Closure.Foundation.StateBoundary

namespace Cpp

def typeFrameDeclObject (Γ : TypeEnv) (k : Nat) (x : Ident) (τ : CppType) : Prop :=
  ∃ fr, Γ.scopes[k]? = some fr ∧ fr.decls x = some (.object τ)

def typeFrameDeclRef (Γ : TypeEnv) (k : Nat) (x : Ident) (τ : CppType) : Prop :=
  ∃ fr, Γ.scopes[k]? = some fr ∧ fr.decls x = some (.ref τ)

def runtimeFrameBindsObject (σ : State) (k : Nat) (x : Ident) (τ : CppType) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ fr.binds x = some (.object τ a)

def runtimeFrameBindsRef (σ : State) (k : Nat) (x : Ident) (τ : CppType) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ fr.binds x = some (.ref τ a)

def runtimeFrameOwnsAddress (σ : State) (k : Nat) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ a ∈ fr.locals

def heapLiveTypedAt (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true

def heapInitializedTypedAt (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c v, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true ∧ c.value = some v ∧ ValueCompat v τ

def shadowingCompatible (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ x d, lookupDecl Γ x = some d → ∃ b, lookupBinding σ x = some b ∧ DeclMatchesBinding d b

def frameDepthAgreement (Γ : TypeEnv) (σ : State) : Prop :=
  Γ.scopes.length = σ.scopes.length

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

def nextFreshAgainstOwned (σ : State) : Prop :=
  σ.heap σ.next = none ∧ ∀ (k : Nat) (fr : ScopeFrame), σ.scopes[k]? = some fr → σ.next ∉ fr.locals

def refBindingsNeverOwned (σ : State) : Prop :=
  ∀ (k : Nat) (fr : ScopeFrame) (x : Ident) (τ : CppType) (a : Nat),
    σ.scopes[k]? = some fr → fr.binds x = some (.ref τ a) → a ∈ fr.locals → ∃ y υ, fr.binds y = some (.object υ a)

structure ScopedTypedStateConcreteKernel (Γ : TypeEnv) (σ : State) : Prop where
  frameDepth : frameDepthAgreement Γ σ
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
