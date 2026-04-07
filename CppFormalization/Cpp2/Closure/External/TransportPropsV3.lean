import CppFormalization.Cpp2.Closure.External.TransportV3

namespace Cpp

/-!
# Closure.External.TransportPropsV3

Small transport / proof-irrelevance lemmas used by higher builder-style
boundary comparison arguments.

These are intentionally separated from `BuilderV3` so that the builder layer
keeps its main role: packaging a certificate family into the V3 external
interfaces. The lemmas here are about dependent equality bookkeeping, not
about the conceptual content of the builder itself.
-/

/-- `BodyAdequacyCI` is propositionally proof-irrelevant at a fixed profile. -/
theorem bodyAdequacy_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p : BodyControlProfile Γ st}
    (A B : BodyAdequacyCI Γ σ st p) :
    A = B := by
  cases A
  cases B
  simp

end Cpp
