import CppFormalization.Cpp2.Closure.External.GlueV3

namespace Cpp

/-!
# Closure.External.AdequacyKernelV3

Kernel for the last external semantic bottleneck in the V3 route.

Design:
- fix the canonical runtime / reflection packages chosen by `mkRuntime` / `mkReflection`,
- isolate the real semantic obligations into two kernel statements:
  * normal-soundness for the canonical profile,
  * return-soundness for the canonical profile,
- package those two statements into a `BodyAdequacyCI` witness,
- finally package the compatibility predicate plus that adequacy builder into
  a concrete `VerifiedExternalGlueV3`.

Crucial point:
- the kernel statements no longer depend on a pre-existing glue object `G`;
- they depend only on an abstract compatibility predicate `Compat`;
- therefore this file can *produce* a concrete glue object instead of assuming one.
-/

section CanonicalPieces

/-- Canonical runtime package chosen by the std fragment. -/
noncomputable def canonicalRuntimePiecesV3
    {F : VerifiedStdFragmentV3}
    {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st) :
    RuntimePiecesV3 Γ σ st :=
  F.mkRuntime huses hruntime

/-- Canonical reflection package chosen by the reflection fragment. -/
noncomputable def canonicalReflectionPiecesV3
    {R : VerifiedReflectionFragmentV3}
    {m : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    ReflectionPiecesV3 Γ st :=
  R.mkReflection hgen hrefl

/-- Canonical control profile used by the external adequacy glue. -/
noncomputable def canonicalProfileV3
    {R : VerifiedReflectionFragmentV3}
    {m : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    BodyControlProfile Γ st :=
  (canonicalReflectionPiecesV3 (m := m) (Γ := Γ) (st := st) hgen hrefl).profile

/-- Canonical structural boundary chosen by the reflection package. -/
noncomputable def canonicalStructuralV3
    {R : VerifiedReflectionFragmentV3}
    {m : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    BodyStructuralBoundary Γ st :=
  (canonicalReflectionPiecesV3 (m := m) (Γ := Γ) (st := st) hgen hrefl).structural

/-- Canonical dynamic boundary chosen by the std/runtime package. -/
noncomputable def canonicalDynamicV3
    {F : VerifiedStdFragmentV3}
    {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st) :
    BodyDynamicBoundary Γ σ st :=
  (canonicalRuntimePiecesV3 (n := n) (Γ := Γ) (σ := σ) (st := st) huses hruntime).dynamic

/-- Canonical core-membership witness chosen by the reflection package. -/
noncomputable def canonicalCoreV3
    {R : VerifiedReflectionFragmentV3}
    {m : R.Meta} {Γ : TypeEnv} {st : CppStmt}
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st) :
    CoreBigStepFragment st :=
  (canonicalReflectionPiecesV3 (m := m) (Γ := Γ) (st := st) hgen hrefl).core

end CanonicalPieces

section Compatibility

/-- Abstract compatibility predicate used by the adequacy kernel. -/
abbrev CompatibilityPredicateV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3) : Type :=
  F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

end Compatibility

section KernelStatements

/--
Kernel obligation for the canonical profile: any actual normal execution must be
accounted for by the canonical normal summary.
-/
axiom canonical_profile_normal_sound_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st)
    {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.normalOut = some out

/--
Kernel obligation for the canonical profile: any actual return execution must be
accounted for by the canonical return summary.
-/
axiom canonical_profile_return_sound_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ st (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out

end KernelStatements

section Packaging

/--
Package the two canonical kernel statements into the exact `BodyAdequacyCI`
required by the V3 glue interface.
-/
noncomputable def canonicalAdequacyOfSoundnessV3
   {R : VerifiedReflectionFragmentV3}
   {m : R.Meta}
   {Γ : TypeEnv} {σ : State} {st : CppStmt}
   (hgen : R.generates m st)
   (hrefl : R.supportsReflection m Γ st)
   (hNormal :
      ∀ {σ' : State},
        BigStepStmt σ st .normal σ' →
        ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
          (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.normalOut = some out)
   (hReturn :
      ∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ st (.returnResult rv) σ' →
        ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
          (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl).summary.returnOut = some out) :
   BodyAdequacyCI Γ σ st
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl) := by
  refine
    { normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep
    exact hNormal hstep
  · intro rv σ' hstep
    exact hReturn hstep

/--
Canonical adequacy witness obtained by applying the two kernel axioms to the
chosen compatibility predicate.
-/
noncomputable def canonicalAdequacyV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huses : F.uses n)
    (hruntime : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hrefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    BodyAdequacyCI Γ σ st
      (canonicalProfileV3 (R := R) (m := m) (Γ := Γ) (st := st) hgen hrefl) :=
  canonicalAdequacyOfSoundnessV3
    hgen hrefl
    (fun {_} hstep =>
      canonical_profile_normal_sound_v3
        (F := F) (R := R) Compat
        huses hruntime hgen hrefl hcompat hstep)
    (fun {_} {_} hstep =>
      canonical_profile_return_sound_v3
        (F := F) (R := R) Compat
        huses hruntime hgen hrefl hcompat hstep)

/--
Turn a compatibility predicate plus the adequacy kernel into a concrete V3 glue
object.
-/
noncomputable def canonicalGlueV3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R) :
    VerifiedExternalGlueV3 F R where
  compatible := Compat
  mkAdequacy := by
    intro n m Γ σ st huses hruntime hgen hrefl hcompat
    exact
      canonicalAdequacyV3
        (F := F) (R := R) Compat
        huses hruntime hgen hrefl hcompat

end Packaging

end Cpp
