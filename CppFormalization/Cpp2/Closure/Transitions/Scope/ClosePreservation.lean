import CppFormalization.Cpp2.Closure.Transitions.Major.CloseScopeTopFrameExtension

namespace Cpp

/-!
# Closure.Transitions.Scope.ClosePreservation

Canonical public entry point for close-scope transition facts.

The main close-scope theorem is the general top-frame-extension version:

`closeScope_preserves_outer_from_topFrameExtension`.

This is the mathematically natural form: closing a runtime scope removes the top
runtime frame and restricts the type environment to the outer fragment.  The old
`pushTypeScope Γ -> Γ` theorem is now just the empty-top-frame specialization.
-/

/--
Specialization of the general top-frame-extension close-scope theorem to the
ordinary `pushTypeScope` case.

This should be the preferred replacement for directly depending on the older
special-purpose close-scope assembly theorem.
-/
theorem closeScope_preserves_outer_from_pushTypeScope
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hclose
  exact
    closeScope_preserves_outer_from_topFrameExtension
      (topFrameExtensionOf_pushTypeScope Γ) hσ hclose

end Cpp
