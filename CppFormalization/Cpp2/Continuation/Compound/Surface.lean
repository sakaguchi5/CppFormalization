import CppFormalization.Cpp2.Continuation.Compound.Seq.Surface
import CppFormalization.Cpp2.Continuation.Compound.Cons.Surface
import CppFormalization.Cpp2.Continuation.Compound.While.Surface

namespace Cpp
namespace CompoundContinuation

/-!
# CompoundContinuation surface

Seq, cons, and while are instances of one compound-continuation pattern.

| compound | selected route | continuation target | boundary | lifting |
| --- | --- | --- | --- | --- |
| `s; t` | left normal | statement tail `t` | `StmtContinuationDynamicBoundary` | `seqNormal` |
| `s :: ss` | head normal | block tail `ss` | `BlockContinuationDynamicBoundary` | `consNormal` |
| `while c body` | body normal/continue | same while | `StmtContinuationDynamicBoundary` | `whileTrueNormal` / `whileTrueContinue` |
-/

inductive ProgramContractKind where
  | stmtReplay
  | blockReplay
  | conditionReplay
  | bodyReplay
  | loadReadability
  | pointerDerefStability
deriving DecidableEq, Repr

inductive TheoremObligationKind where
  | postStatePreservation
  | staticProfileAlignment
  | adequacy
  | exitLifting
  | tailLifting
deriving DecidableEq, Repr

inductive ProofDemandKind where
  | localProgress
  | tailClosure
  | recursionDemand
deriving DecidableEq, Repr

end CompoundContinuation
end Cpp
