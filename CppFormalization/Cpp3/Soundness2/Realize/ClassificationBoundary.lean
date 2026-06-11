import CppFormalization.Cpp3.Soundness2.Realize.LocalControl
import CppFormalization.Cpp3.Soundness2.Realize.ScopeExit
import CppFormalization.Cpp3.Soundness2.Realize.LoopBehavior
import CppFormalization.Cpp3.Soundness2.Source.ClosedInternal

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationBoundary

Boundary-level statement/block classifier layer.

This is the classifier shape that naturally follows local control and scope
exit: recursive compound cases produce post-state `Boundary.*Boundary` objects,
not reconstructed source packages.  Source-level classifiers are recovered only
as wrappers around these boundary-level classifiers.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Source-level realized classifier for closed-internal statements. -/
structure StmtClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      Source.StmtBoundarySource Γ σ st →
        Source.ClosedStmtSoundness σ st

/-- Source-level realized classifier for closed-internal block bodies. -/
structure BlockClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.BlockBoundarySource Γ σ body →
        Source.ClosedBlockSoundness σ body

/-- Boundary-level statement classifier.

This is the recursive core consumed after local-control handoffs. -/
structure BoundaryStmtClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      Boundary.StmtBoundary Γ σ st →
        Source.ClosedStmtSoundness σ st

/-- Boundary-level block classifier. -/
structure BoundaryBlockClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Boundary.BlockBoundary Γ σ body →
        Source.ClosedBlockSoundness σ body

namespace BoundaryStmtClassifierRealization

/-- Recover the source-level statement classifier from the boundary-level core. -/
def toSourceRealization
    (K : BoundaryStmtClassifierRealization) :
    StmtClassifierRealization where
  classify := by
    intro Γ σ st source
    exact K.classify source.toBoundary

end BoundaryStmtClassifierRealization

namespace BoundaryBlockClassifierRealization

/-- Recover the source-level block classifier from the boundary-level core. -/
def toSourceRealization
    (K : BoundaryBlockClassifierRealization) :
    BlockClassifierRealization where
  classify := by
    intro Γ σ body source
    exact K.classify source.toBoundary

end BoundaryBlockClassifierRealization

end Realize
end Soundness2
end Cpp3
