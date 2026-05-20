import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Basic
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Place
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Value
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Block
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Stmt
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Continuation
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Stability
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Surface

/-!
# CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2

Clean-room route-local seq-tail replay package.

This aggregate intentionally does not import the current `SeqTailReplay.*`
modules.  It rebuilds the same mathematical content around selected routes,
post-state replay, and continuation boundaries.
-/
