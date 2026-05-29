import CppFormalization.Cpp2.Language.Syntax

namespace Cpp

/--
Read-places whose address lookup is replay-stable across heap-only updates by
syntax shape alone.

Current honest base keeps only variable places.
-/
inductive ReplayStableReadPlace : PlaceExpr → Prop where
  | var {x : Ident} :
      ReplayStableReadPlace (.var x)

end Cpp
