import CppFormalization.Cpp2.Closure.External.CoherenceV3
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.TransportV3

General transport / cast lemmas used by both the ready route and concrete
families.

These are logically external-layer infrastructure rather than toy-specific
facts.  Keeping them here prevents concrete examples from becoming accidental
containers for generic dependent-equality plumbing.
-/

/-- Transport adequacy across propositional equality of control profiles. -/
def transportAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (h : p = q) :
    BodyAdequacyCI Γ σ st p → BodyAdequacyCI Γ σ st q := by
  intro ha
  cases h
  exact ha

@[simp] theorem transportAdequacy_rfl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p : BodyControlProfile Γ st}
    (ha : BodyAdequacyCI Γ σ st p) :
    transportAdequacy rfl ha = ha := by
  rfl

/-- Ready adequacy transports along equality of ready witnesses. -/
theorem toAdequacy_transport_of_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {r₁ r₂ : BodyReadyCI Γ σ st}
    (h : r₁ = r₂) :
    transportAdequacy (congrArg BodyReadyCI.toProfile h) r₁.toAdequacy =
      r₂.toAdequacy := by
  cases h
  rfl

/-- Alias used when an equality is conceptually viewed as an index cast. -/
abbrev castBodyAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (h : p = q) :
    BodyAdequacyCI Γ σ st p → BodyAdequacyCI Γ σ st q :=
  transportAdequacy h

@[simp] theorem castBodyAdequacy_rfl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p : BodyControlProfile Γ st}
    (ha : BodyAdequacyCI Γ σ st p) :
    castBodyAdequacy rfl ha = ha := by
  rfl

@[simp] theorem castBodyAdequacy_symm_cast
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (h : p = q)
    (hp : BodyAdequacyCI Γ σ st p) :
    castBodyAdequacy h.symm (castBodyAdequacy h hp) = hp := by
  cases h
  rfl

@[simp] theorem castBodyAdequacy_cast_symm
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (h : p = q)
    (hp : BodyAdequacyCI Γ σ st q) :
    castBodyAdequacy h (castBodyAdequacy h.symm hp) = hp := by
  cases h
  rfl

/-- Extensionality for closure boundaries with adequacy compared after the
necessary profile-index transport. -/
@[ext (iff := false)] theorem BodyClosureBoundaryCI.ext
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {b₁ b₂ : BodyClosureBoundaryCI Γ σ st}
    (hstruct : b₁.structural = b₂.structural)
    (hprof : b₁.profile = b₂.profile)
    (hdyn : b₁.dynamic = b₂.dynamic)
    (hadequ : castBodyAdequacy hprof b₁.adequacy = b₂.adequacy) :
    b₁ = b₂ := by
  cases b₁
  cases b₂
  cases hstruct
  cases hprof
  cases hdyn
  simp at hadequ
  cases hadequ
  rfl

/-- Cast an external visible package across equality of its indices. -/
def castExternalPiecesV3
    {Γ₁ Γ₂ : TypeEnv} {σ₁ σ₂ : State} {st₁ st₂ : CppStmt}
    (hΓ : Γ₁ = Γ₂) (hσ : σ₁ = σ₂) (hst : st₁ = st₂) :
    ExternalPiecesV3 Γ₁ σ₁ st₁ → ExternalPiecesV3 Γ₂ σ₂ st₂ := by
  intro p
  cases hΓ
  cases hσ
  cases hst
  exact p

/-- Cast visible pieces across equality of their indices. -/
def castVisiblePiecesV3
    {Γ₁ Γ₂ : TypeEnv} {σ₁ σ₂ : State} {st₁ st₂ : CppStmt}
    (hΓ : Γ₁ = Γ₂) (hσ : σ₁ = σ₂) (hst : st₁ = st₂) :
    VisiblePiecesV3 Γ₁ σ₁ st₁ → VisiblePiecesV3 Γ₂ σ₂ st₂ := by
  intro p
  cases hΓ
  cases hσ
  cases hst
  exact p

@[simp] theorem castExternalPiecesV3_rfl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : ExternalPiecesV3 Γ σ st) :
    castExternalPiecesV3 rfl rfl rfl p = p := by
  rfl

@[simp] theorem castVisiblePiecesV3_rfl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (p : VisiblePiecesV3 Γ σ st) :
    castVisiblePiecesV3 rfl rfl rfl p = p := by
  rfl

@[simp] theorem castExternalPiecesV3_toVisiblePieces
    {Γ₁ Γ₂ : TypeEnv} {σ₁ σ₂ : State} {st₁ st₂ : CppStmt}
    (hΓ : Γ₁ = Γ₂) (hσ : σ₁ = σ₂) (hst : st₁ = st₂)
    (p : ExternalPiecesV3 Γ₁ σ₁ st₁) :
    (castExternalPiecesV3 hΓ hσ hst p).toVisiblePieces =
      castVisiblePiecesV3 hΓ hσ hst p.toVisiblePieces := by
  cases hΓ
  cases hσ
  cases hst
  rfl

/-- Rebuilding a closure boundary after transporting adequacy along the profile
comparison yields the same boundary. -/
theorem mkBodyClosureBoundaryCI_profile_transport
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {hs : BodyStructuralBoundary Γ st}
    {hd : BodyDynamicBoundary Γ σ st}
    {p q : BodyControlProfile Γ st}
    (h : p = q)
    (ha : BodyAdequacyCI Γ σ st p) :
    mkBodyClosureBoundaryCI hs q hd (transportAdequacy h ha) =
      mkBodyClosureBoundaryCI hs p hd ha := by
  cases h
  rfl

end Cpp
