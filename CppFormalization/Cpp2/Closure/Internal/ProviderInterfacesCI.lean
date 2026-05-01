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
A soundness-carrying external compatibility package.

The existing `CompatibilityPredicateV3` is only a predicate.  This record is a
future replacement target for the two generic canonical-profile soundness
axioms: soundness should be carried by the external compatibility/interface, not
globally assumed.
-/
structure ExternalSoundnessProviderV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3) : Type where
  compatible : CompatibilityPredicateV3 F R

  normalSound :
    ∀ {n : F.Name} {m : R.Meta}
      {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (_ : F.uses n)
      (_ : F.supportsRuntime n Γ σ st)
      (hgen : R.generates m st)
      (hrefl : R.supportsReflection m Γ st)
      (_ : compatible n m Γ σ st)
      {σ' : State}
      (_ : BigStepStmt σ st .normal σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
        (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st)
          hgen hrefl).summary.normalOut = some out

  returnSound :
    ∀ {n : F.Name} {m : R.Meta}
      {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (_ : F.uses n)
      (_ : F.supportsRuntime n Γ σ st)
      (hgen : R.generates m st)
      (hrefl : R.supportsReflection m Γ st)
      (_ : compatible n m Γ σ st)
      {rv : Option Value} {σ' : State}
      (_ : BigStepStmt σ st (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
        (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st)
          hgen hrefl).summary.returnOut = some out

namespace ExternalSoundnessProviderV3

/--
Build a concrete external glue object from soundness-carrying compatibility,
without using the generic canonical-profile soundness axioms.
-/
noncomputable def toGlue
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (S : ExternalSoundnessProviderV3 F R) :
    VerifiedExternalGlueV3 F R where
  compatible := S.compatible
  mkAdequacy := by
    intro n m Γ σ st huses hruntime hgen hrefl hcompat
    exact
      canonicalAdequacyOfSoundnessV3
        (R := R) (m := m) (Γ := Γ) (σ := σ) (st := st)
        hgen hrefl
        (fun {_} hstep =>
          S.normalSound huses hruntime hgen hrefl hcompat hstep)
        (fun {_} {_} hstep =>
          S.returnSound huses hruntime hgen hrefl hcompat hstep)

end ExternalSoundnessProviderV3

end Cpp
