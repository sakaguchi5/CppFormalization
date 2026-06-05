import CppFormalization.Cpp3.Core.Syntax

namespace Cpp3

/--
Read-places whose address lookup is replay-stable across heap-only updates by
syntax shape alone.

Current honest base keeps only variable places.
-/
inductive ReplayStableReadPlace : PlaceExpr → Prop where
  | var {x : Ident} :
      ReplayStableReadPlace (.var x)

end Cpp3
