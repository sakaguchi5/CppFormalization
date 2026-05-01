import CppFormalization.Cpp2.Closure.External.CoherenceV3
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

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

@[ext (iff := false)] theorem BodyClosureBoundaryCI.ext
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {b₁ b₂ : BodyClosureBoundaryCI Γ σ st}
    (hstruct : b₁.structural = b₂.structural)
    (hstatic : b₁.static = b₂.static)
    (hdyn : b₁.dynamic = b₂.dynamic)
    (hadequ :
      castBodyAdequacy (congrArg BodyStaticBoundaryCI.profile hstatic) b₁.adequacy =
        b₂.adequacy) :
    b₁ = b₂ := by
  cases b₁
  cases b₂
  cases hstruct
  cases hstatic
  cases hdyn
  simp at hadequ
  cases hadequ
  rfl


@[simp] theorem castBodyAdequacy_eq_transport
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (h : p = q)
    (ha : BodyAdequacyCI Γ σ st p) :
    castBodyAdequacy h ha = h ▸ ha := by
  cases h
  rfl

@[simp] theorem castBodyAdequacy_symm_cast
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (e : p = q)
    (h : BodyAdequacyCI Γ σ st p) :
    castBodyAdequacy e.symm (castBodyAdequacy e h) = h := by
  cases e
  rfl

theorem castBodyAdequacy_match_static
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {s₁ s₂ : BodyStaticBoundaryCI Γ st}
    (ha : BodyAdequacyCI Γ σ st s₁.profile)
    (h : s₁ = s₂) :
    castBodyAdequacy
      (Eq.symm (congrArg BodyStaticBoundaryCI.profile h))
      (match s₂, h with
       | _, rfl => ha)
      =
      ha := by
  cases h
  rfl

theorem castBodyAdequacy_symm
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (ha : BodyAdequacyCI Γ σ st p)
    (h : p = q) :
    castBodyAdequacy (Eq.symm h) (castBodyAdequacy h ha) = ha := by
  cases h
  rfl

theorem match_toStatic_eq_castBodyAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (ready : BodyReadyCI Γ σ st)
    {s : BodyStaticBoundaryCI Γ st}
    (h : ready.toStatic = s) :
    (match s, h with
     | .(ready.toStatic), rfl => ready.toAdequacy)
    =
    castBodyAdequacy
      (congrArg BodyStaticBoundaryCI.profile h)
      ready.toAdequacy := by
  cases h
  rfl



theorem mkBodyClosureBoundaryCI_static_transport
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {hs : BodyStructuralBoundary Γ st}
    {hstatic₁ hstatic₂ : BodyStaticBoundaryCI Γ st}
    {hd : BodyDynamicBoundary Γ σ st}
    (hstatic : hstatic₁ = hstatic₂)
    (ha : BodyAdequacyCI Γ σ st hstatic₁.profile) :
    mkBodyClosureBoundaryCI hs hstatic₂ hd
      (transportAdequacy (congrArg BodyStaticBoundaryCI.profile hstatic) ha) =
    mkBodyClosureBoundaryCI hs hstatic₁ hd ha := by
  cases hstatic
  rfl

end Cpp
