import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3

namespace Cpp

/-!
# Closure.External.ToyReadyInstanceV3

A first concrete inhabited V3 instance.

Purpose:
- show that the V3 target-indexed ready route is not merely abstract,
- provide a minimal witness-carrying family whose artifacts are intentionally
  small and canonical,
- separate "the API is inhabited" from the later task of building a more
  realistic external family.

Design:
- one certificate packages a single target `(Γ, σ, st)` together with
  an integrated `BodyReadyCI Γ σ st` witness and a `CoreBigStepFragment st`
  witness,
- the std-side artifact and reflection-side artifact are both this same
  certificate type,
- compatibility simply says the two artifacts are the same certificate and the
  target indices match that certificate.
-/

structure ToyReadyCertificate where
  Γ : TypeEnv
  σ : State
  st : CppStmt
  ready : BodyReadyCI Γ σ st
  core : CoreBigStepFragment st

/-- Toy std/runtime-side fragment: one certificate carries one dynamic target. -/
def toyStdFragmentV3 : VerifiedStdFragmentV3 where
  Name := ToyReadyCertificate
  uses := fun _ => True
  supportsDynamic := fun n Γ σ st => Γ = n.Γ ∧ σ = n.σ ∧ st = n.st
  mkDynamic := by
    intro n Γ σ st _ hsupp
    rcases hsupp with ⟨rfl, rfl, rfl⟩
    exact n.ready.toDynamic

/-- Toy reflection-side fragment: one certificate carries one generated target. -/
def toyReflectionFragmentV3 : VerifiedReflectionFragmentV3 where
  Meta := ToyReadyCertificate
  generates := fun m st => st = m.st
  supportsStructural := fun m Γ st => Γ = m.Γ ∧ st = m.st
  supportsProfile := fun m Γ st => Γ = m.Γ ∧ st = m.st
  mkStructural := by
    intro m Γ st _ hsupp
    rcases hsupp with ⟨rfl, rfl⟩
    exact m.ready.toStructural
  mkProfile := by
    intro m Γ st _ hsupp
    rcases hsupp with ⟨rfl, rfl⟩
    exact m.ready.toProfile
  mkCore := by
    intro m st hgen
    rcases hgen with rfl
    exact m.core

/-- Toy ready-style assembly: compatibility just identifies the two certificates. -/
def toyReadyAssemblyV3 :
    VerifiedExternalReadyAssemblyV3 toyStdFragmentV3 toyReflectionFragmentV3 where
  compatible := fun n m Γ σ st =>
    n = m ∧ Γ = n.Γ ∧ σ = n.σ ∧ st = n.st
  mkReady := by
    intro n m Γ σ st _ _ _ _ _ hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    exact n.ready

/-- Canonical witnesses showing that a certificate instantiates the toy family. -/
theorem toy_uses (c : ToyReadyCertificate) :
    toyStdFragmentV3.uses c := by
  trivial

theorem toy_supportsDynamic (c : ToyReadyCertificate) :
    toyStdFragmentV3.supportsDynamic c c.Γ c.σ c.st := by
  exact ⟨rfl, rfl, rfl⟩

theorem toy_generates (c : ToyReadyCertificate) :
    toyReflectionFragmentV3.generates c c.st := by
  rfl

theorem toy_supportsStructural (c : ToyReadyCertificate) :
    toyReflectionFragmentV3.supportsStructural c c.Γ c.st := by
  exact ⟨rfl, rfl⟩

theorem toy_supportsProfile (c : ToyReadyCertificate) :
    toyReflectionFragmentV3.supportsProfile c c.Γ c.st := by
  exact ⟨rfl, rfl⟩

theorem toy_compatible (c : ToyReadyCertificate) :
    toyReadyAssemblyV3.compatible c c c.Γ c.σ c.st := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The canonical explicit V3 pieces assembled from a toy certificate. -/
def toyExternalPiecesV3 (c : ToyReadyCertificate) :
    ExternalPiecesV3 c.Γ c.σ c.st :=
  externalPieces_of_ready_v3 toyReadyAssemblyV3
    (toy_uses c)
    (toy_supportsDynamic c)
    (toy_generates c)
    (toy_supportsStructural c)
    (toy_supportsProfile c)
    (toy_compatible c)

/-- The toy `mkReady` really returns the packaged witness itself. -/
theorem toyReadyAssemblyV3_mkReady_eq
    (c : ToyReadyCertificate) :
    toyReadyAssemblyV3.mkReady
      (toy_uses c)
      (toy_supportsDynamic c)
      (toy_generates c)
      (toy_supportsStructural c)
      (toy_supportsProfile c)
      (toy_compatible c)
    = c.ready := by
  cases c
  unfold toy_compatible toy_supportsProfile toy_supportsStructural
    toy_generates toy_supportsDynamic toy_uses
  simp [toyReadyAssemblyV3]

/-- Toy specialization of the generic profile comparison lemma. -/
theorem toyExternalPiecesV3_profile
    (c : ToyReadyCertificate) :
    (toyExternalPiecesV3 c).profile = c.ready.toProfile := by
  simpa [toyExternalPiecesV3, toyReadyAssemblyV3_mkReady_eq c] using
    (externalPieces_of_ready_v3_profile
      (A := toyReadyAssemblyV3)
      (huse := toy_uses c)
      (hsuppDyn := toy_supportsDynamic c)
      (hgen := toy_generates c)
      (hsuppStruct := toy_supportsStructural c)
      (hsuppProf := toy_supportsProfile c)
      (hcompat := toy_compatible c))

/--
Toy specialization of the generic adequacy transport lemma.

This is exactly the phenomenon that motivated the generalization:
`adequacy` lives over `profile`, so comparison requires transport.
-/
theorem toyExternalPiecesV3_adequacy
    (c : ToyReadyCertificate) :
    transportAdequacy (toyExternalPiecesV3_profile c).symm c.ready.toAdequacy
      = (toyExternalPiecesV3 c).adequacy := by
  simpa [toyExternalPiecesV3, toyReadyAssemblyV3_mkReady_eq c, toyExternalPiecesV3_profile c] using
    (externalPieces_of_ready_v3_adequacy
      (A := toyReadyAssemblyV3)
      (huse := toy_uses c)
      (hsuppDyn := toy_supportsDynamic c)
      (hgen := toy_generates c)
      (hsuppStruct := toy_supportsStructural c)
      (hsuppProf := toy_supportsProfile c)
      (hcompat := toy_compatible c))

/-- The assembled boundary produced by the toy route is the expected one. -/
theorem toyExternalPiecesV3_boundary
    (c : ToyReadyCertificate) :
    (toyExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
  simpa [toyExternalPiecesV3, toyReadyAssemblyV3_mkReady_eq c] using
    (externalPieces_of_ready_v3_boundary
      (A := toyReadyAssemblyV3)
      (huse := toy_uses c)
      (hsuppDyn := toy_supportsDynamic c)
      (hgen := toy_generates c)
      (hsuppStruct := toy_supportsStructural c)
      (hsuppProf := toy_supportsProfile c)
      (hcompat := toy_compatible c))

/-- First concrete inhabited statement-level closure instance for V3. -/
theorem toy_ready_certificate_closure
    (c : ToyReadyCertificate) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  exact
    reflective_std_closure_theorem_from_ready_v3
      toyReadyAssemblyV3
      (toy_uses c)
      (toy_supportsDynamic c)
      (toy_generates c)
      (toy_supportsStructural c)
      (toy_supportsProfile c)
      (toy_compatible c)

/-- Function-body variant of the first concrete inhabited V3 instance. -/
theorem toy_ready_certificate_function_body_closure
    (c : ToyReadyCertificate) :
    (∃ ex σ', BigStepFunctionBody c.σ c.st ex σ') ∨ BigStepStmtDiv c.σ c.st := by
  exact
    reflective_std_function_body_closure_from_ready_v3
      toyReadyAssemblyV3
      (toy_uses c)
      (toy_supportsDynamic c)
      (toy_generates c)
      (toy_supportsStructural c)
      (toy_supportsProfile c)
      (toy_compatible c)

end Cpp
