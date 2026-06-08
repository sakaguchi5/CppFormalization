import CppFormalization.Cpp3.Semantics.Kernel.Classification

/-!
# CppFormalization.Cpp3.Soundness.Target

Closed internal C++ fragment soundness targets.

This layer fixes the semantic target of Cpp3 soundness before the real
structural proof is added.  No external-call specification appears here:
the closed fragment has no opaque external-call syntax, so every executed
behavior must be represented by Cpp3 syntax and Cpp3 semantics.
-/

namespace Cpp3
namespace Soundness

/-- Statement-level closed-fragment soundness target. -/
def ClosedStmtSoundness (σ : State) (st : CppStmt) : Prop :=
  Semantics.StmtClassified σ st

/-- Block-level closed-fragment soundness target. -/
def ClosedBlockSoundness (σ : State) (body : StmtBlock) : Prop :=
  Semantics.BlockClassified σ body

/-- Function-body closed-fragment soundness target.

Function-body finite success is intentionally narrower than arbitrary
statement termination: top-level `break`/`continue` are not successful
function-body outcomes.  Divergence remains a valid classified outcome.
-/
def ClosedFunctionBodySoundness (σ : State) (body : CppStmt) : Prop :=
  Semantics.FunctionBodyClassified σ body

/-- Marker for the adopted final-theorem scope of Cpp3. -/
def closedInternalFragmentSoundnessPolicy : String :=
  "Cpp3 soundness is for the closed internal C++ fragment: no opaque external-call syntax is part of the target."

end Soundness
end Cpp3
