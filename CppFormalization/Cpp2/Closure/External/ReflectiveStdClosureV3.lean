import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.AssembleV3

namespace Cpp

/-!
# Closure.External.ReflectiveStdClosureV3

Final wrapper for the V3 external closure route.

Policy after locating the remaining lie:
- explicit glue route remains available as a low-level specialization;
- generic `Compat` route inherited from `AdequacyKernelV3` remains available as
  a provisional shortcut;
- the honest canonical theorem route is the contract-based route
  `Compat + CanonicalAdequacyContractsV3`.
-/

/-- Low-level specialization using an explicit glue object. -/
theorem reflective_std_function_body_closure_v3_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    G.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st := assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.function_body_progress_or_diverges p.core p.toBodyBoundary

/-- Low-level specialization using an explicit glue object. -/
theorem reflective_std_closure_theorem_v3_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    G.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st := assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.stmt_terminates_or_diverges p.core p.toBodyBoundary

/--
Provisional shortcut driven only by a compatibility predicate.

This route is retained for compatibility with the current generic kernel, but it
should not be regarded as the honest final semantic public surface.
-/
theorem reflective_std_function_body_closure_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    Compat n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesFromCompatV3 (F := F) (R := R) Compat huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.function_body_progress_or_diverges p.core p.toBodyBoundary

/-- Provisional shortcut driven only by a compatibility predicate. -/
theorem reflective_std_closure_theorem_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    Compat n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesFromCompatV3 (F := F) (R := R) Compat huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.stmt_terminates_or_diverges p.core p.toBodyBoundary

/--
Honest canonical public route driven by:
- a compatibility predicate, and
- the explicit pair of adequacy contracts.
-/
theorem reflective_std_function_body_closure_v3_ofContracts
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    Compat n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesFromContractsV3
      (F := F) (R := R) Compat H huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.function_body_progress_or_diverges p.core p.toBodyBoundary

/-- Honest canonical public route driven by explicit adequacy contracts. -/
theorem reflective_std_closure_theorem_v3_ofContracts
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    Compat n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesFromContractsV3
      (F := F) (R := R) Compat H huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.stmt_terminates_or_diverges p.core p.toBodyBoundary

/-- Contract-based route is definitionally the explicit route with `canonicalGlueV3_ofContracts`. -/
theorem reflective_std_function_body_closure_v3_ofContracts_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    reflective_std_function_body_closure_v3_ofContracts
      (F := F) (R := R) Compat H (n := n) (m := m) (Γ := Γ) (σ := σ) (st := st)
      =
    reflective_std_function_body_closure_v3_explicit
      (F := F) (R := R)
      (canonicalGlueV3_ofContracts (F := F) (R := R) Compat H)
      (n := n) (m := m) (Γ := Γ) (σ := σ) (st := st) := by
  rfl

/-- Likewise for the statement-level closure theorem. -/
theorem reflective_std_closure_theorem_v3_ofContracts_eq_explicit
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (Compat : CompatibilityPredicateV3 F R)
    (H : CanonicalAdequacyContractsV3 R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    reflective_std_closure_theorem_v3_ofContracts
      (F := F) (R := R) Compat H (n := n) (m := m) (Γ := Γ) (σ := σ) (st := st)
      =
    reflective_std_closure_theorem_v3_explicit
      (F := F) (R := R)
      (canonicalGlueV3_ofContracts (F := F) (R := R) Compat H)
      (n := n) (m := m) (Γ := Γ) (σ := σ) (st := st) := by
  rfl

end Cpp
