import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3

namespace Cpp

/-!
# Closure.External.ToyReadyInstanceV3

First concrete inhabited ready-route instance for the Stage 2A redesign.

Main redesign changes reflected here:
- the std side now returns `RuntimePiecesV3`,
- the reflection side now returns one package containing
  `(structural, profile, core)`,
- the ready assembly must expose explicit coherence with those chosen pieces.
-/

structure ToyReadyCertificate where
  Γ : TypeEnv
  σ : State
  st : CppStmt
  ready : BodyReadyCI Γ σ st
  core : CoreBigStepFragment st

/-- Toy std/runtime-side fragment: one certificate carries one runtime target. -/
def toyStdFragmentV3 : VerifiedStdFragmentV3 where
  Name := ToyReadyCertificate
  uses := fun _ => True
  supportsRuntime := fun n Γ σ st => Γ = n.Γ ∧ σ = n.σ ∧ st = n.st
  mkRuntime := by
    intro n Γ σ st _ hsupp
    rcases hsupp with ⟨rfl, rfl, rfl⟩
    exact { dynamic := n.ready.toDynamic }

/-- Toy reflection-side fragment: one certificate carries one reflection target. -/
def toyReflectionFragmentV3 : VerifiedReflectionFragmentV3 where
  Meta := ToyReadyCertificate
  generates := fun m st => st = m.st
  supportsReflection := fun m Γ st => Γ = m.Γ ∧ st = m.st
  mkReflection := by
    intro m Γ st _ hsupp
    rcases hsupp with ⟨rfl, rfl⟩
    exact
      { structural := m.ready.structural
        static := m.ready.static
        core := m.core }

/-- Toy ready-style assembly: compatibility just identifies the two certificates. -/
def toyReadyAssemblyV3 :
    VerifiedExternalReadyAssemblyV3 toyStdFragmentV3 toyReflectionFragmentV3 where
  compatible := fun n m Γ σ st =>
    n = m ∧ Γ = n.Γ ∧ σ = n.σ ∧ st = n.st
  mkReady := by
    intro n m Γ σ st _ _ _ _ hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    exact n.ready
  dynamic_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRun with ⟨_, _, _⟩
    rfl
  structural_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRefl with ⟨_, _⟩
    rfl
  static_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRefl with ⟨_, _⟩
    rfl

/-- Canonical witnesses showing that a certificate instantiates the toy family. -/
theorem toy_uses (c : ToyReadyCertificate) :
    toyStdFragmentV3.uses c := by
  trivial

theorem toy_supportsRuntime (c : ToyReadyCertificate) :
    toyStdFragmentV3.supportsRuntime c c.Γ c.σ c.st := by
  exact ⟨rfl, rfl, rfl⟩

theorem toy_generates (c : ToyReadyCertificate) :
    toyReflectionFragmentV3.generates c c.st := by
  rfl

theorem toy_supportsReflection (c : ToyReadyCertificate) :
    toyReflectionFragmentV3.supportsReflection c c.Γ c.st := by
  exact ⟨rfl, rfl⟩

theorem toy_compatible (c : ToyReadyCertificate) :
    toyReadyAssemblyV3.compatible c c c.Γ c.σ c.st := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The reflection package chosen from a toy certificate is the obvious one. -/
theorem toyReflectionFragmentV3_structural (c : ToyReadyCertificate) :
    (toyReflectionFragmentV3.mkReflection
      (toy_generates c)
      (toy_supportsReflection c)).structural = c.ready.toStructural := by
  cases c
  rfl

theorem toyReflectionFragmentV3_profile (c : ToyReadyCertificate) :
    (toyReflectionFragmentV3.mkReflection
      (toy_generates c)
      (toy_supportsReflection c)).static.profile = c.ready.static.profile := by
  cases c
  unfold toyReflectionFragmentV3 toy_generates toy_supportsReflection
  dsimp

@[simp] theorem BodyReadyCI.toProfile_eq_static_profile
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    h.toProfile = h.static.profile := by
  rfl

theorem toyReflectionFragmentV3_core (c : ToyReadyCertificate) :
    (toyReflectionFragmentV3.mkReflection
      (toy_generates c)
      (toy_supportsReflection c)).core = c.core := by
  cases c
  rfl

/-- The canonical explicit V3 pieces assembled from a toy certificate. -/
def toyExternalPiecesV3 (c : ToyReadyCertificate) :
    ExternalPiecesV3 c.Γ c.σ c.st :=
  externalPieces_of_ready_v3 toyReadyAssemblyV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toy_compatible c)

/-- The toy `mkReady` really returns the packaged witness itself. -/
theorem toyReadyAssemblyV3_mkReady_eq (c : ToyReadyCertificate) :
    toyReadyAssemblyV3.mkReady
      (toy_uses c)
      (toy_supportsRuntime c)
      (toy_generates c)
      (toy_supportsReflection c)
      (toy_compatible c) = c.ready := by
  cases c
  unfold toyReadyAssemblyV3 toy_compatible
  dsimp

theorem toyReflectionFragmentV3_static_eq (c : ToyReadyCertificate) :
    (toyReflectionFragmentV3.mkReflection
      (toy_generates c)
      (toy_supportsReflection c)).static = c.ready.static := by
  cases c with
  | mk Γ σ st ready core =>
      unfold toyReflectionFragmentV3 toy_generates toy_supportsReflection
      dsimp

/-- The assembled profile is exactly the reflection-selected toy profile. -/
theorem toyExternalPiecesV3_profile (c : ToyReadyCertificate) :
    (toyExternalPiecesV3 c).static.profile = c.ready.static.profile := by
  unfold toyExternalPiecesV3
  simp [externalPieces_of_ready_v3, toyReflectionFragmentV3_static_eq]

theorem toyReady_toProfile_eq (c : ToyReadyCertificate) :
    c.ready.static.profile =
      (toyReadyAssemblyV3.mkReady
        (toy_uses c)
        (toy_supportsRuntime c)
        (toy_generates c)
        (toy_supportsReflection c)
        (toy_compatible c)).static.profile := by
  simp [toyReadyAssemblyV3_mkReady_eq c]

theorem toyReadyAssemblyV3_profile_eq
    (c : ToyReadyCertificate) :
    (toyReadyAssemblyV3.mkReady
      (toy_uses c)
      (toy_supportsRuntime c)
      (toy_generates c)
      (toy_supportsReflection c)
      (toy_compatible c)).static.profile =
    (toyReflectionFragmentV3.mkReflection
      (toy_generates c)
      (toy_supportsReflection c)).static.profile := by
  simpa using congrArg BodyStaticBoundaryCI.profile
    (toyReadyAssemblyV3.static_eq
      (toy_uses c)
      (toy_supportsRuntime c)
      (toy_generates c)
      (toy_supportsReflection c)
      (toy_compatible c))

theorem toyExternalPiecesV3_adequacy (c : ToyReadyCertificate) :
    (toyExternalPiecesV3 c).adequacy =
      transportAdequacy
        (toyReadyAssemblyV3_profile_eq c)
        ((toyReadyAssemblyV3.mkReady
          (toy_uses c)
          (toy_supportsRuntime c)
          (toy_generates c)
          (toy_supportsReflection c)
          (toy_compatible c)).toAdequacy) := by
  -- 定義を展開して構造を露出させる
  unfold toyExternalPiecesV3 externalPieces_of_ready_v3
  -- 各コンポーネントが c.ready に集約されることを利用して simp
  simp



private theorem toyReady_toAdequacy_transport (c : ToyReadyCertificate) :
    transportAdequacy (toyReady_toProfile_eq c) c.ready.toAdequacy =
      (toyReadyAssemblyV3.mkReady
        (toy_uses c)
        (toy_supportsRuntime c)
        (toy_generates c)
        (toy_supportsReflection c)
        (toy_compatible c)).toAdequacy := by
  -- 1. まず c を分解
  cases c with | mk Γ σ st ready core =>
  unfold toyReady_toProfile_eq toy_compatible
  unfold transportAdequacy
  simp
  rfl



/-- Alternate display of adequacy using the packaged `c.ready` witness. -/
theorem toyExternalPiecesV3_adequacy_ready (c : ToyReadyCertificate) :
    (toyExternalPiecesV3 c).adequacy =
      transportAdequacy
        (toyReadyAssemblyV3_profile_eq c)
        (transportAdequacy (toyReady_toProfile_eq c) c.ready.toAdequacy) := by
  calc
    (toyExternalPiecesV3 c).adequacy =
        transportAdequacy
          (toyReadyAssemblyV3_profile_eq c)
          ((toyReadyAssemblyV3.mkReady
            (toy_uses c)
            (toy_supportsRuntime c)
            (toy_generates c)
            (toy_supportsReflection c)
            (toy_compatible c)).toAdequacy) := by
              exact toyExternalPiecesV3_adequacy c
    _ =
        transportAdequacy
          (toyReadyAssemblyV3_profile_eq c)
          (transportAdequacy (toyReady_toProfile_eq c) c.ready.toAdequacy) := by
            rw [toyReady_toAdequacy_transport c]

/-- The assembled boundary produced by the toy route is the expected one. -/
theorem toyExternalPiecesV3_boundary (c : ToyReadyCertificate) :
    (toyExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
  simpa [toyExternalPiecesV3, toyReadyAssemblyV3_mkReady_eq c] using
    (externalPieces_of_ready_v3_boundary
      (A := toyReadyAssemblyV3)
      (huse := toy_uses c)
      (hsuppRun := toy_supportsRuntime c)
      (hgen := toy_generates c)
      (hsuppRefl := toy_supportsReflection c)
      (hcompat := toy_compatible c))

/-- First concrete inhabited statement-level closure instance for the new V3 route. -/
theorem toy_ready_certificate_closure (c : ToyReadyCertificate) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  exact reflective_std_closure_theorem_from_ready_v3
    toyReadyAssemblyV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toy_compatible c)

/-- Function-body variant of the first concrete inhabited V3 instance. -/
theorem toy_ready_certificate_function_body_closure (c : ToyReadyCertificate) :
    (∃ ex σ', BigStepFunctionBody c.σ c.st ex σ') ∨ BigStepStmtDiv c.σ c.st := by
  exact reflective_std_function_body_closure_from_ready_v3
    toyReadyAssemblyV3
    (toy_uses c)
    (toy_supportsRuntime c)
    (toy_generates c)
    (toy_supportsReflection c)
    (toy_compatible c)

end Cpp
