import CppFormalization.Cpp2.Closure.Internal.LoopBodyFunctionClosureCI
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel
import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3

namespace Cpp

/-!
# Closure.Internal.ProviderInterfacesCI

Provider interfaces introduced as secondary assets.  These do not remove the
current shells by themselves; they make the later replacement targets smaller
and more explicit.
-/

/--
Provider form of loop-body local progress/divergence.

This lets specialized body classes supply theorem-backed progress while the
generic shell remains isolated.
-/
structure LoopBodyProgressProviderCI
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  progress :
    LoopBodyBoundaryCI Γ σ body →
      (∃ ctrl σ', BigStepStmt σ body ctrl σ') ∨ BigStepStmtDiv σ body

/--
Replay-stable primitive loop bodies already have theorem-backed local
progress/divergence.
-/
def replayStablePrimitiveLoopBodyProgressProviderCI
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body) :
    LoopBodyProgressProviderCI Γ σ body :=
  { progress := by
      intro hloop
      exact replay_stable_primitive_loop_body_function_progress_or_diverges_ci
        hstable hloop }

/--
A smaller read-side transport interface for the current replay-stable read
fragment, where `ReplayStableReadPlace` is still variable-only.

This is a target for decomposing `AssignReadTransportKernel`, not a replacement
for the full alias-sensitive story.
-/
structure AssignVarReadTransportKernel : Type where
  varReady_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {x : Ident} {q : PlaceExpr} {e : ValExpr} {τ : CppType},
      ScopedTypedStateConcrete Γ σ' →
      PlaceReadyConcrete Γ σ (.var x) τ →
      BigStepStmt σ (.assign q e) .normal σ' →
      PlaceReadyConcrete Γ σ' (.var x) τ

  varLoadReadable_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {x : Ident} {q : PlaceExpr} {e : ValExpr} {τ : CppType},
      ScopedTypedStateConcrete Γ σ' →
      (∃ a, BigStepPlace σ (.var x) a ∧ CellReadableTyped σ a τ) →
      BigStepStmt σ (.assign q e) .normal σ' →
      (∃ a, BigStepPlace σ' (.var x) a ∧ CellReadableTyped σ' a τ)

/--
A concrete compatible runtime/reflection case for a fixed statement and state.

This packages the runtime name, reflection metadata, support proofs, and the
actual compatibility proof into one value.  The profile itself is still the
reflection-side canonical profile, but soundness is stated only for cases that
are genuinely compatible with the runtime side.
-/
structure ExternalCompatibleCaseV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3)
    (compatible : CompatibilityPredicateV3 F R)
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  n : F.Name
  m : R.Meta
  huses : F.uses n
  hruntime : F.supportsRuntime n Γ σ st
  hgen : R.generates m st
  hrefl : R.supportsReflection m Γ st
  hcompat : compatible n m Γ σ st

/--
A witness-producing external compatibility package.

The primitive fields now return subtype witnesses rather than `Prop`-level
existentials.  This matches the direction of `BodyAdequacyWitnessCI`: an
external interface that wants to construct downstream Type-level packages should
carry the selected canonical-profile output as data.  Proof-only soundness is
recovered below by forgetting the witnesses.
-/
structure ExternalSoundnessCompatibilityV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3) : Type where
  compatible : CompatibilityPredicateV3 F R

  normalWitness :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (C : ExternalCompatibleCaseV3 F R compatible Γ σ st)
      {σ' : State},
      BigStepStmt σ st .normal σ' →
      { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} //
        (canonicalProfileV3
          (R := R) (m := C.m) (Γ := Γ) (st := st)
          C.hgen C.hrefl).summary.normalOut = some out }

  returnWitness :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (C : ExternalCompatibleCaseV3 F R compatible Γ σ st)
      {rv : Option Value} {σ' : State},
      BigStepStmt σ st (.returnResult rv) σ' →
      { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} //
        (canonicalProfileV3
          (R := R) (m := C.m) (Γ := Γ) (st := st)
          C.hgen C.hrefl).summary.returnOut = some out }

namespace ExternalSoundnessCompatibilityV3

/-- Forget the witness-producing normal provider to proof-only soundness. -/
theorem normalSound
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (S : ExternalSoundnessCompatibilityV3 F R)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (C : ExternalCompatibleCaseV3 F R S.compatible Γ σ st)
    {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      (canonicalProfileV3
        (R := R) (m := C.m) (Γ := Γ) (st := st)
        C.hgen C.hrefl).summary.normalOut = some out := by
  let w := S.normalWitness C hstep
  exact ⟨w.val, w.property⟩

/-- Forget the witness-producing return provider to proof-only soundness. -/
theorem returnSound
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (S : ExternalSoundnessCompatibilityV3 F R)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (C : ExternalCompatibleCaseV3 F R S.compatible Γ σ st)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ st (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      (canonicalProfileV3
        (R := R) (m := C.m) (Γ := Γ) (st := st)
        C.hgen C.hrefl).summary.returnOut = some out := by
  let w := S.returnWitness C hstep
  exact ⟨w.val, w.property⟩

/--
Build a concrete external glue object from soundness-carrying compatibility,
without using the generic canonical-profile soundness axioms.
-/
noncomputable def toGlue
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (S : ExternalSoundnessCompatibilityV3 F R) :
    VerifiedExternalGlueV3 F R where
  compatible := S.compatible
  mkAdequacy := by
    intro n m Γ σ st huses hruntime hgen hrefl hcompat

    let C : ExternalCompatibleCaseV3 F R S.compatible Γ σ st :=
      { n := n
        m := m
        huses := huses
        hruntime := hruntime
        hgen := hgen
        hrefl := hrefl
        hcompat := hcompat }

    exact
      canonicalAdequacyOfSoundnessV3
        (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st)
        hgen hrefl
        (fun {_} hstep =>
          normalSound S C hstep)
        (fun {_} {_} hstep =>
          returnSound S C hstep)

end ExternalSoundnessCompatibilityV3

end Cpp
