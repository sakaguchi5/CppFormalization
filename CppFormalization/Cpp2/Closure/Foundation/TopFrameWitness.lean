import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Foundation.TopFrameWitness

Tiny bridge from top-scope freshness to an explicit top-frame witness.

This is useful for certificate-level APIs that need a concrete witness
`Γ.scopes[0]? = some Γfr` after a `currentTypeScopeFresh Γ x` assumption.
It is not specific to object-declaration external fragments.
-/

/-- `currentTypeScopeFresh` already guarantees that the type environment has a
non-empty scope stack, so we can recover the top frame as a subtype witness. -/
def topTypeFrameWitness_of_currentTypeScopeFresh
    {Γ : TypeEnv} {x : Ident}
    (h : currentTypeScopeFresh Γ x) :
    {Γfr : TypeFrame // Γ.scopes[0]? = some Γfr} := by
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at h
  | cons fr frs =>
      exact ⟨fr, by simp⟩

end Cpp
