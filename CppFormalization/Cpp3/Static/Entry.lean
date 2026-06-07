import CppFormalization.Cpp3.Static.ControlProfile

/-!
# CppFormalization.Cpp3.Static.Entry

Static entry witnesses for the program points that later runtime Boundary and
Continuation layers will refine.

These witnesses are deliberately pre-runtime: they say that a program point is a
well-formed static entry point and expose the syntactic control/profile surface.
They do not assert that any concrete `State` is ready.
-/

namespace Cpp3
namespace Static

/-- Static entry for a statement at type environment `Γ`. -/
structure StmtEntryWitness (Γ : TypeEnv) (st : CppStmt) : Type where
  formed : StaticStmtFormed st
  profile : StmtControlProfile st

/-- Static entry for a block body at type environment `Γ`. -/
structure BlockEntryWitness (Γ : TypeEnv) (ss : StmtBlock) : Type where
  formed : StaticBlockFormed ss
  profile : BlockControlProfile ss

namespace StmtEntryWitness

/-- Canonical statement entry from static formation. -/
def canonical
    (Γ : TypeEnv) {st : CppStmt} (h : StaticStmtFormed st) :
    StmtEntryWitness Γ st where
  formed := h
  profile := StmtControlProfile.canonical h

end StmtEntryWitness

namespace BlockEntryWitness

/-- Canonical block-body entry from static formation. -/
def canonical
    (Γ : TypeEnv) {ss : StmtBlock} (h : StaticBlockFormed ss) :
    BlockEntryWitness Γ ss where
  formed := h
  profile := BlockControlProfile.canonical h

end BlockEntryWitness

/-- Static entry for the tail of a sequence after a statically normal head. -/
structure SeqTailEntry
    (Γ Θ : TypeEnv) (head tail : CppStmt) : Type where
  headFormed : StaticStmtFormed head
  headNormal : StaticStmtControl head .normalK
  tailEntry : StmtEntryWitness Θ tail

/-- Static entry for the tail of a block body after a statically normal head. -/
structure BlockTailEntry
    (Γ Θ : TypeEnv) (head : CppStmt) (tail : StmtBlock) : Type where
  headFormed : StaticStmtFormed head
  headNormal : StaticStmtControl head .normalK
  tailEntry : BlockEntryWitness Θ tail

/-- Static branch choice.  Runtime selected routes will refine this shape with a
condition value and post-condition state. -/
inductive StaticBranchChoice where
  | thenBranch
  | elseBranch
  deriving DecidableEq, Repr

/-- Static entry for the branch selected by an `if` condition. -/
inductive SelectedBranchEntry
    (Γ Γc : TypeEnv) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : StaticBranchChoice → Type where
  | thenEntry :
      StaticCondFormed cond →
      StmtEntryWitness Γc thenBranch →
      StaticStmtFormed elseBranch →
      SelectedBranchEntry Γ Γc cond thenBranch elseBranch .thenBranch

  | elseEntry :
      StaticCondFormed cond →
      StaticStmtFormed thenBranch →
      StmtEntryWitness Γc elseBranch →
      SelectedBranchEntry Γ Γc cond thenBranch elseBranch .elseBranch

/-- Static while entry.  It exposes only the condition/body entry surfaces; the
runtime backedge boundary is a later Stability/Continuation obligation. -/
structure WhileEntry
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Type where
  condFormed : StaticCondFormed cond
  bodyEntry : StmtEntryWitness Γc body

/-- Static entry for an opened block body. -/
structure OpenedBlockEntry
    (Γ Γopen : TypeEnv) (body : StmtBlock) : Type where
  scopeEntry : StaticBlockScopeEntry Γ Γopen
  bodyEntry : BlockEntryWitness Γopen body

end Static
end Cpp3
