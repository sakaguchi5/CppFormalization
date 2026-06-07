import CppFormalization.Cpp3.Stability.Scope

/-!
# CppFormalization.Cpp3.Stability.Registry

Composite registry surfaces for stability packages.

These registries are intentionally shallow.  They are convenient handoff points
for the next `Continuation` layer and for later proof files that replace abstract
certificates with concrete theorems.
-/

namespace Cpp3
namespace Stability

/-- Registry for the main selected-route stability surfaces of a statement. -/
structure StmtStabilityRegistry (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  entry : Boundary.StmtBoundary Γ σ st
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Registry for the main selected-route stability surfaces of a block body. -/
structure BlockStabilityRegistry (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  entry : Boundary.BlockBoundary Γ σ body
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Registry for function-body stability.

This does not assert final soundness.  It only packages the stability surface that
`Soundness` should later consume to rule out unclassified stuckness. -/
structure FunctionBodyStabilityRegistry
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  boundary : Boundary.FunctionBodyBoundary Γ σ body
  stmtRegistry : StmtStabilityRegistry Γ σ body
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

/-- Classification-facing stability surface for a function body. -/
structure FunctionBodyClassificationStability
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  registry : FunctionBodyStabilityRegistry Γ σ body
  classifiedTarget : Prop
  evidence : StabilityCertificate .soundnessDerived classifiedTarget

end Stability
end Cpp3
