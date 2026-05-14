import CppFormalization.Cpp2.Core.Syntax

namespace Cpp

/-!
# Lemmas.ReplayStableReadPlace

Small, static vocabulary for read-place replay across assignment-like updates.

This file is intentionally below Closure/Internal: it contains no transport
axiom and only classifies the syntactic read places whose address lookup is
known to be replay-stable by shape alone.
-/

/--
Read-places whose address lookup is replay-stable across a heap write without
committing to arbitrary alias-sensitive replay.

Current honest base keeps only variable places.
-/
inductive ReplayStableReadPlace : PlaceExpr → Prop where
  | var {x : Ident} :
      ReplayStableReadPlace (.var x)

end Cpp
