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


/-!
## Provider classification used by closure proofs

A closure proof usually separates three roles.

* Source closure provider:
  closes or executes the source sub-execution and obtains a control exit or
  divergence.

* Successor provider:
  given a specific source exit route, reconstructs the next target boundary.

* Closure shell:
  once the target boundary is available, recursively closes that target.

Successor providers are semantic C++ control-flow facts.  Closure shells are
proof architecture.
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
