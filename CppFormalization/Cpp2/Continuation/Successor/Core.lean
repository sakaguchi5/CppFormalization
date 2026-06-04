--import CppFormalization.Cpp2.Language.Syntax

namespace Cpp
namespace ControlSuccessor

/-!
# Continuation.Successor.Core

C++ control-successor vocabulary.

A successor edge is the semantic fact that once a sub-execution exits with a
specific control result, the next continuation target can be reconstructed.

Examples:

* sequence/block cons: head normal -> tail;
* while backedge: body normal/continue -> next iteration;
* block statement: opened body normal/return -> close scope;
* conditional: condition result -> selected branch.

This layer intentionally avoids a fully generic dependent target type.  Concrete
successor shapes are introduced in dedicated files.
-/

/-- Lightweight classification of common C++ successor situations. -/
inductive SuccessorKind where
  | seqNormal
  | blockConsNormal
  | whileBackedgeNormal
  | whileBackedgeContinue
  | iteTrue
  | iteFalse
  | blockCloseNormal
  | blockCloseReturn
  deriving DecidableEq, Repr

end ControlSuccessor
end Cpp
