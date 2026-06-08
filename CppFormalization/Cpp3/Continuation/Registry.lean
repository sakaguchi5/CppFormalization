import CppFormalization.Cpp3.Continuation.Primitive
import CppFormalization.Cpp3.Continuation.Seq
import CppFormalization.Cpp3.Continuation.Block
import CppFormalization.Cpp3.Continuation.Branch
import CppFormalization.Cpp3.Continuation.While

/-!
# CppFormalization.Cpp3.Continuation.Registry

Composite continuation registries.

These registries are intentionally shallow.  They are handoff points for later
Soundness files, not final progress or preservation theorems.
-/

namespace Cpp3
namespace Continuation

/-- Registry for statement-level continuation information. -/
structure StmtContinuationRegistry
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  entry : Boundary.StmtBoundary Γ σ st
  stability : Stability.StmtStabilityRegistry Γ σ st
  readyForSoundness : Prop
  certificate : ContinuationCertificate readyForSoundness

/-- Registry for block-body continuation information. -/
structure BlockContinuationRegistry
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  entry : Boundary.BlockBoundary Γ σ body
  stability : Stability.BlockStabilityRegistry Γ σ body
  readyForSoundness : Prop
  certificate : ContinuationCertificate readyForSoundness

/-- Registry for function-body continuation information. -/
structure FunctionBodyContinuationRegistry
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  boundary : Boundary.FunctionBodyBoundary Γ σ body
  stability : Stability.FunctionBodyStabilityRegistry Γ σ body
  stmtContinuation : StmtContinuationRegistry Γ σ body
  readyForSoundness : Prop
  certificate : ContinuationCertificate readyForSoundness

end Continuation
end Cpp3
