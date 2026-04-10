import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3
import CppFormalization.Cpp2.Closure.External.AssembleLemmasV3
import CppFormalization.Cpp2.Closure.External.CanonicityV3
import CppFormalization.Cpp2.Closure.External.ToyReadyInstanceV3

namespace Cpp

/-!
# Closure.External.ToyGlueInstanceV3

First concrete inhabited low-level glue instance for the redesigned V3.

Role in the roadmap:
- show that the low-level glue route is inhabited on the same toy family,
- show that the direct ready route and the direct glue route agree at the
  visible-package level and at the official boundary quotient,
- show that the toy family also satisfies the Stage 2C canonicity vocabulary
  in the compatible-relative form that is actually valid for this toy setup.
-/

/-- Toy low-level glue: compatibility is the same canonical certificate identity. -/
def toyGlueV3 : VerifiedExternalGlueV3 toyStdFragmentV3 toyReflectionFragmentV3 where
  compatible := toyReadyAssemblyV3.compatible
  mkAdequacy := by
    intro n m Γ σ st _ _ hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRefl with ⟨_, _⟩
    simpa [toyReflectionFragmentV3] using n.ready.toAdequacy

theorem toyGlue_compatible (c : ToyReadyCertificate) :
    toyGlueV3.compatible c c c.Γ c.σ c.st := by
  exact toy_compatible c

/-- Canonical explicit V3 pieces assembled from the toy low-level glue route. -/
noncomputable def toyGlueExternalPiecesV3
    (c : ToyReadyCertificate) :
    ExternalPiecesV3 c.Γ c.σ c.st :=
  assembleExternalPiecesV3 toyGlueV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toyGlue_compatible c)

theorem toyGlueExternalPiecesV3_profile
    (c : ToyReadyCertificate) :
    (toyGlueExternalPiecesV3 c).profile = c.ready.toProfile := by
  have h :=
    assembleExternalPiecesV3_profile
      (G := toyGlueV3)
      (huse := toy_uses c)
      (hsuppRun := toy_supportsRuntime c)
      (hgen := toy_generates c)
      (hsuppRefl := toy_supportsReflection c)
      (hcompat := toyGlue_compatible c)
  simpa [toyGlueExternalPiecesV3, toyReflectionFragmentV3_profile c] using h

theorem toyGlueExternalPiecesV3_structural
    (c : ToyReadyCertificate) :
    (toyGlueExternalPiecesV3 c).structural = c.ready.toStructural := by
  have h :=
    assembleExternalPiecesV3_structural
      (G := toyGlueV3)
      (huse := toy_uses c)
      (hsuppRun := toy_supportsRuntime c)
      (hgen := toy_generates c)
      (hsuppRefl := toy_supportsReflection c)
      (hcompat := toyGlue_compatible c)
  simp

theorem toyGlueExternalPiecesV3_dynamic
    (c : ToyReadyCertificate) :
    (toyGlueExternalPiecesV3 c).dynamic = c.ready.toDynamic := by
  have h :=
    assembleExternalPiecesV3_dynamic
      (G := toyGlueV3)
      (huse := toy_uses c)
      (hsuppRun := toy_supportsRuntime c)
      (hgen := toy_generates c)
      (hsuppRefl := toy_supportsReflection c)
      (hcompat := toyGlue_compatible c)
  cases c
  simp

theorem toyGlueExternalPiecesV3_core
    (c : ToyReadyCertificate) :
    (toyGlueExternalPiecesV3 c).core = c.core := by
  have h :=
    assembleExternalPiecesV3_core
      (G := toyGlueV3)
      (huse := toy_uses c)
      (hsuppRun := toy_supportsRuntime c)
      (hgen := toy_generates c)
      (hsuppRefl := toy_supportsReflection c)
      (hcompat := toyGlue_compatible c)
  simp

theorem toyGlueExternalPiecesV3_boundary_adequacy
    (c : ToyReadyCertificate) :
    castBodyAdequacy (toyGlueExternalPiecesV3_profile c)
      ((toyGlueExternalPiecesV3 c).toBodyBoundary.adequacy) =
      (c.ready.toClosureBoundary).adequacy := by
  cases c
  rfl

theorem toyGlueExternalPiecesV3_boundary
    (c : ToyReadyCertificate) :
    (toyGlueExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
  ext
  · exact toyGlueExternalPiecesV3_structural c
  · exact toyGlueExternalPiecesV3_profile c
  · exact toyGlueExternalPiecesV3_dynamic c
  · exact toyGlueExternalPiecesV3_boundary_adequacy c

/-- The glue-side visible package is exactly the canonical package of the toy target. -/
theorem toyGlueExternalPiecesV3_packageCoherent
    (c : ToyReadyCertificate) :
    PackageCoherentV3
      (toyGlueExternalPiecesV3 c).toVisiblePieces
      (canonicalVisiblePiecesV3
        (toy_uses c) (toy_supportsRuntime c)
        (toy_generates c) (toy_supportsReflection c)) := by
  simpa [toyGlueExternalPiecesV3] using
    (assembleExternalPiecesV3_packageCoherent
      (G := toyGlueV3)
      (huse := toy_uses c)
      (hsuppRun := toy_supportsRuntime c)
      (hgen := toy_generates c)
      (hsuppRefl := toy_supportsReflection c)
      (hcompat := toyGlue_compatible c))

noncomputable def toyGlueVisiblePiecesAt
    {n : toyStdFragmentV3.Name}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hsuppRun : toyStdFragmentV3.supportsRuntime n Γ σ st) :
    VisiblePiecesV3 Γ σ st := by
  rcases hsuppRun with ⟨hΓ, hσ, hst⟩
  exact castVisiblePiecesV3 hΓ.symm hσ.symm hst.symm ((toyGlueExternalPiecesV3 n).toVisiblePieces)

noncomputable def toyGlueExternalPiecesAt
    {n : toyStdFragmentV3.Name}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hsuppRun : toyStdFragmentV3.supportsRuntime n Γ σ st) :
    ExternalPiecesV3 Γ σ st := by
  rcases hsuppRun with ⟨hΓ, hσ, hst⟩
  exact castExternalPiecesV3 hΓ.symm hσ.symm hst.symm (toyGlueExternalPiecesV3 n)

theorem toyGlueExternalPiecesAt_toVisiblePieces
    {n : toyStdFragmentV3.Name}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hsuppRun : toyStdFragmentV3.supportsRuntime n Γ σ st) :
    (toyGlueExternalPiecesAt hsuppRun).toVisiblePieces =
      castVisiblePiecesV3
        (by
          rcases hsuppRun with ⟨hΓ, _, _⟩
          exact hΓ.symm)
        (by
          rcases hsuppRun with ⟨_, hσ, _⟩
          exact hσ.symm)
        (by
          rcases hsuppRun with ⟨_, _, hst⟩
          exact hst.symm)
        ((toyGlueExternalPiecesV3 n).toVisiblePieces) := by
  rcases hsuppRun with ⟨rfl, rfl, rfl⟩
  rfl

theorem toyCanonicalVisiblePiecesV3_packageCoherent_compatible
    {n : toyStdFragmentV3.Name} {m : toyReflectionFragmentV3.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : toyStdFragmentV3.uses n)
    (hsuppRun : toyStdFragmentV3.supportsRuntime n Γ σ st)
    (hgen : toyReflectionFragmentV3.generates m st)
    (hsuppRefl : toyReflectionFragmentV3.supportsReflection m Γ st)
    (hcompat : toyReadyAssemblyV3.compatible n m Γ σ st) :
    PackageCoherentV3
      (canonicalVisiblePiecesV3 huse hsuppRun hgen hsuppRefl)
      (toyGlueExternalPiecesAt hsuppRun).toVisiblePieces := by
  cases n with
  | mk Γn σn stn ready_n core_n =>
    cases m with
    | mk Γm σm stm ready_m core_m =>
      simp [toyGlueExternalPiecesAt, castExternalPiecesV3,
            toyStdFragmentV3, toyReflectionFragmentV3] at hsuppRun hgen hsuppRefl hcompat ⊢
      rcases hsuppRun with ⟨rfl, rfl, rfl⟩
      rcases hgen with rfl
      rcases hsuppRefl with ⟨rfl, _⟩
      simp [toyReadyAssemblyV3] at hcompat
      rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
      simpa using
        (toyGlueExternalPiecesV3_packageCoherent
          { Γ := Γ, σ := σ, st := st, ready := ready_n, core := core_n }).symm

theorem toyCanonicalVisiblePiecesV3_wellDefined_compatible_fixed_runtime
    {n : toyStdFragmentV3.Name} {m₁ m₂ : toyReflectionFragmentV3.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : toyStdFragmentV3.uses n)
    (hsuppRun : toyStdFragmentV3.supportsRuntime n Γ σ st)
    (hgen₁ : toyReflectionFragmentV3.generates m₁ st)
    (hsuppRefl₁ : toyReflectionFragmentV3.supportsReflection m₁ Γ st)
    (hcompat₁ : toyReadyAssemblyV3.compatible n m₁ Γ σ st)
    (hgen₂ : toyReflectionFragmentV3.generates m₂ st)
    (hsuppRefl₂ : toyReflectionFragmentV3.supportsReflection m₂ Γ st)
    (hcompat₂ : toyReadyAssemblyV3.compatible n m₂ Γ σ st) :
    canonicalVisiblePiecesV3 huse hsuppRun hgen₁ hsuppRefl₁ =
      canonicalVisiblePiecesV3 huse hsuppRun hgen₂ hsuppRefl₂ := by
  have hcoh₁ :
      canonicalVisiblePiecesV3 huse hsuppRun hgen₁ hsuppRefl₁ =
        (toyGlueExternalPiecesAt hsuppRun).toVisiblePieces := by
    simpa [PackageCoherentV3] using
      (toyCanonicalVisiblePiecesV3_packageCoherent_compatible
        huse hsuppRun hgen₁ hsuppRefl₁ hcompat₁)
  have hcoh₂ :
      canonicalVisiblePiecesV3 huse hsuppRun hgen₂ hsuppRefl₂ =
        (toyGlueExternalPiecesAt hsuppRun).toVisiblePieces := by
    simpa [PackageCoherentV3] using
      (toyCanonicalVisiblePiecesV3_packageCoherent_compatible
        huse hsuppRun hgen₂ hsuppRefl₂ hcompat₂)
  exact hcoh₁.trans hcoh₂.symm

theorem toyCanonicalVisiblePiecesV3_wellDefined_compatible
    {n₁ n₂ : toyStdFragmentV3.Name} {m₁ m₂ : toyReflectionFragmentV3.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hn : n₁ = n₂)
    (huse₁ : toyStdFragmentV3.uses n₁)
    (hsuppRun₁ : toyStdFragmentV3.supportsRuntime n₁ Γ σ st)
    (hgen₁ : toyReflectionFragmentV3.generates m₁ st)
    (hsuppRefl₁ : toyReflectionFragmentV3.supportsReflection m₁ Γ st)
    (hcompat₁ : toyReadyAssemblyV3.compatible n₁ m₁ Γ σ st)
    (huse₂ : toyStdFragmentV3.uses n₂)
    (hsuppRun₂ : toyStdFragmentV3.supportsRuntime n₂ Γ σ st)
    (hgen₂ : toyReflectionFragmentV3.generates m₂ st)
    (hsuppRefl₂ : toyReflectionFragmentV3.supportsReflection m₂ Γ st)
    (hcompat₂ : toyReadyAssemblyV3.compatible n₂ m₂ Γ σ st) :
    canonicalVisiblePiecesV3 huse₁ hsuppRun₁ hgen₁ hsuppRefl₁ =
      canonicalVisiblePiecesV3 huse₂ hsuppRun₂ hgen₂ hsuppRefl₂ := by
  cases hn
  exact toyCanonicalVisiblePiecesV3_wellDefined_compatible_fixed_runtime
    huse₁ hsuppRun₁ hgen₁ hsuppRefl₁ hcompat₁ hgen₂ hsuppRefl₂ hcompat₂

theorem toyCanonicalVisiblePiecesV3_packageCoherent_under_same_runtime
    {n₁ n₂ : toyStdFragmentV3.Name} {m₁ m₂ : toyReflectionFragmentV3.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hn : n₁ = n₂)
    (huse₁ : toyStdFragmentV3.uses n₁)
    (hsuppRun₁ : toyStdFragmentV3.supportsRuntime n₁ Γ σ st)
    (hgen₁ : toyReflectionFragmentV3.generates m₁ st)
    (hsuppRefl₁ : toyReflectionFragmentV3.supportsReflection m₁ Γ st)
    (hcompat₁ : toyReadyAssemblyV3.compatible n₁ m₁ Γ σ st)
    (huse₂ : toyStdFragmentV3.uses n₂)
    (hsuppRun₂ : toyStdFragmentV3.supportsRuntime n₂ Γ σ st)
    (hgen₂ : toyReflectionFragmentV3.generates m₂ st)
    (hsuppRefl₂ : toyReflectionFragmentV3.supportsReflection m₂ Γ st)
    (hcompat₂ : toyReadyAssemblyV3.compatible n₂ m₂ Γ σ st) :
    PackageCoherentV3
      (canonicalVisiblePiecesV3 huse₁ hsuppRun₁ hgen₁ hsuppRefl₁)
      (canonicalVisiblePiecesV3 huse₂ hsuppRun₂ hgen₂ hsuppRefl₂) := by
  have h :=
    toyCanonicalVisiblePiecesV3_wellDefined_compatible
      hn
      huse₁ hsuppRun₁ hgen₁ hsuppRefl₁ hcompat₁
      huse₂ hsuppRun₂ hgen₂ hsuppRefl₂ hcompat₂
  simpa [PackageCoherentV3] using h

theorem toyCanonicalVisiblePiecesV3_packageCoherent_compatible_fixed_runtime
    {n : toyStdFragmentV3.Name} {m₁ m₂ : toyReflectionFragmentV3.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : toyStdFragmentV3.uses n)
    (hsuppRun : toyStdFragmentV3.supportsRuntime n Γ σ st)
    (hgen₁ : toyReflectionFragmentV3.generates m₁ st)
    (hsuppRefl₁ : toyReflectionFragmentV3.supportsReflection m₁ Γ st)
    (hcompat₁ : toyReadyAssemblyV3.compatible n m₁ Γ σ st)
    (hgen₂ : toyReflectionFragmentV3.generates m₂ st)
    (hsuppRefl₂ : toyReflectionFragmentV3.supportsReflection m₂ Γ st)
    (hcompat₂ : toyReadyAssemblyV3.compatible n m₂ Γ σ st) :
    PackageCoherentV3
      (canonicalVisiblePiecesV3 huse hsuppRun hgen₁ hsuppRefl₁)
      (canonicalVisiblePiecesV3 huse hsuppRun hgen₂ hsuppRefl₂) := by
  simpa [PackageCoherentV3] using
    toyCanonicalVisiblePiecesV3_wellDefined_compatible_fixed_runtime
      huse hsuppRun hgen₁ hsuppRefl₁ hcompat₁
      hgen₂ hsuppRefl₂ hcompat₂

/-- Concrete package-level route coherence on the first inhabited family. -/
theorem toy_ready_vs_glue_packageCoherent
    (c : ToyReadyCertificate) :
    PackageCoherentV3
      (toyExternalPiecesV3 c).toVisiblePieces
      (toyGlueExternalPiecesV3 c).toVisiblePieces := by
  change (toyExternalPiecesV3 c).toVisiblePieces = (toyGlueExternalPiecesV3 c).toVisiblePieces
  calc
    (toyExternalPiecesV3 c).toVisiblePieces =
        canonicalVisiblePiecesV3
          (toy_uses c) (toy_supportsRuntime c)
          (toy_generates c) (toy_supportsReflection c) := by
      rfl
    _ = (toyGlueExternalPiecesV3 c).toVisiblePieces := by
      symm
      exact toyGlueExternalPiecesV3_packageCoherent c

/-- Concrete official boundary coherence on the first inhabited family. -/
theorem toy_ready_vs_glue_boundaryCoherent
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (toyExternalPiecesV3 c)
      (toyGlueExternalPiecesV3 c) := by
  change (toyExternalPiecesV3 c).toBodyBoundary = (toyGlueExternalPiecesV3 c).toBodyBoundary
  calc
    (toyExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
      exact toyExternalPiecesV3_boundary c
    _ = (toyGlueExternalPiecesV3 c).toBodyBoundary := by
      symm
      exact toyGlueExternalPiecesV3_boundary c

/-- The induced ready route from the toy glue is package-coherent with the direct glue route. -/
theorem toy_glue_readyInduced_packageCoherent
    (c : ToyReadyCertificate) :
    PackageCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 toyGlueV3)
        (toy_uses c)
        (toy_supportsRuntime c)
        (toy_generates c)
        (toy_supportsReflection c)
        (toyGlue_compatible c)).toVisiblePieces
      (toyGlueExternalPiecesV3 c).toVisiblePieces := by
  exact externalPieces_of_ready_from_glue_v3_packageCoherent
    toyGlueV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toyGlue_compatible c)

/-- The induced ready route from the toy glue is boundary-coherent with the direct glue route. -/
theorem toy_glue_readyInduced_boundaryCoherent
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 toyGlueV3)
        (toy_uses c)
        (toy_supportsRuntime c)
        (toy_generates c)
        (toy_supportsReflection c)
        (toyGlue_compatible c))
      (toyGlueExternalPiecesV3 c) := by
  exact externalPieces_of_ready_from_glue_v3_boundaryCoherent
    toyGlueV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toyGlue_compatible c)

/-- First concrete inhabited statement-level closure instance for the low-level V3 route. -/
theorem toy_glue_certificate_closure
    (c : ToyReadyCertificate) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  exact reflective_std_closure_theorem_v3_via_ready
    toyGlueV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toyGlue_compatible c)

/-- Function-body variant of the first concrete inhabited low-level V3 instance. -/
theorem toy_glue_certificate_function_body_closure
    (c : ToyReadyCertificate) :
    (∃ ex σ', BigStepFunctionBody c.σ c.st ex σ') ∨ BigStepStmtDiv c.σ c.st := by
  exact reflective_std_function_body_closure_v3_via_ready
    toyGlueV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toyGlue_compatible c)

end Cpp
