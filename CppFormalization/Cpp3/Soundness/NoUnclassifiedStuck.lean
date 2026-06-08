import CppFormalization.Cpp3.Soundness.Target

/-!
# CppFormalization.Cpp3.Soundness.NoUnclassifiedStuck

Tiny bridges from closed-fragment soundness targets to the corresponding
"no unclassified stuck" statements.
-/

namespace Cpp3
namespace Soundness

/-- A closed statement soundness proof rules out residual statement stuckness. -/
theorem noStmtUnclassifiedStuck_of_closedStmtSoundness
    {σ : State} {st : CppStmt}
    (h : ClosedStmtSoundness σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st := by
  intro hstuck
  exact hstuck h

/-- A closed block soundness proof rules out residual block stuckness. -/
theorem noBlockUnclassifiedStuck_of_closedBlockSoundness
    {σ : State} {body : StmtBlock}
    (h : ClosedBlockSoundness σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body := by
  intro hstuck
  exact hstuck h

/-- A closed function-body soundness proof rules out residual function-body stuckness. -/
theorem noFunctionBodyUnclassifiedStuck_of_closedFunctionBodySoundness
    {σ : State} {body : CppStmt}
    (h : ClosedFunctionBodySoundness σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body := by
  intro hstuck
  exact hstuck h

end Soundness
end Cpp3
