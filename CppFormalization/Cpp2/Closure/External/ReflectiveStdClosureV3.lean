import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.AssembleV3

namespace Cpp

/-!
# Closure.External.ReflectiveStdClosureV3

V3 final wrapper after the Stage 2A redesign.

There are now two low-level entry routes:
- explicit glue route via `G : VerifiedExternalGlueV3 F R`,
- canonical compatibility route via `Compat : CompatibilityPredicateV3 F R`.

Both feed the same internal roadmap theorem; only the low-level assembly entry
changes.
-/

/-- Original explicit-glue wrapper. -/
theorem reflective_std_function_body_closure_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    G.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.function_body_progress_or_diverges p.core p.toBodyBoundary

/-- Original explicit-glue statement-level wrapper. -/
theorem reflective_std_closure_theorem_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    G.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.stmt_terminates_or_diverges p.core p.toBodyBoundary

/-- Canonical compatibility-based function-body wrapper. -/
theorem reflective_std_function_body_closure_fromCompat_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    Compat n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesFromCompatV3
      (F := F) (R := R) Compat
      huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.function_body_progress_or_diverges p.core p.toBodyBoundary

/-- Canonical compatibility-based statement-level wrapper. -/
theorem reflective_std_closure_theorem_fromCompat_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    Compat n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesFromCompatV3
      (F := F) (R := R) Compat
      huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.stmt_terminates_or_diverges p.core p.toBodyBoundary

/-- The canonical route is definitionally the explicit route with `canonicalGlueV3 Compat`. -/
theorem reflective_std_closure_theorem_fromCompat_v3_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : Compat n m Γ σ st) :
    reflective_std_closure_theorem_fromCompat_v3
      (F := F) (R := R) Compat
      (n := n) (m := m) (Γ := Γ) (σ := σ) (st := st)
      huse hsuppRun hgen hsuppRefl hcompat
      =
    reflective_std_closure_theorem_v3
      (F := F) (R := R)
      (canonicalGlueV3 (F := F) (R := R) Compat)
      (n := n) (m := m) (Γ := Γ) (σ := σ) (st := st)
      huse hsuppRun hgen hsuppRefl hcompat := by
  rfl

end Cpp
