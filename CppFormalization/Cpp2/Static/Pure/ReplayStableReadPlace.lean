import CppFormalization.Cpp2.Core.Syntax

namespace Cpp

/-!
# CppFormalization.Cpp2.Static.Pure.ReplayStableReadPlace

Small, pure static vocabulary for read-place replay across assignment-like
updates.

This file is intentionally below Closure/Internal.  It contains no transport
axiom and only classifies the syntactic read places whose address lookup is
known to be replay-stable by shape alone.
-/
inductive ReplayStableReadPlace : PlaceExpr → Prop where
  | var {x : Ident} :
      ReplayStableReadPlace (.var x)

end Cpp
