import CppFormalization.Cpp3.Core.Types

/-!
Expression, condition, and statement syntax.

`CppCond` is a separate syntactic category for C++ control conditions.  The
current core only supports expression conditions, but `if` and `while` consume
conditions rather than raw value expressions so typing/effects/replay/boundary
facts can be stated once for both constructs.
-/

namespace Cpp3

mutual

inductive PlaceExpr where
  | var   : Ident → PlaceExpr
  | deref : ValExpr → PlaceExpr
  deriving DecidableEq, Repr

inductive ValExpr where
  | litBool : Bool → ValExpr
  | litInt  : Int → ValExpr
  | load    : PlaceExpr → ValExpr
  | addrOf  : PlaceExpr → ValExpr
  | add     : ValExpr → ValExpr → ValExpr
  | sub     : ValExpr → ValExpr → ValExpr
  | mul     : ValExpr → ValExpr → ValExpr
  | eq      : ValExpr → ValExpr → ValExpr
  | lt      : ValExpr → ValExpr → ValExpr
  | not     : ValExpr → ValExpr
  deriving DecidableEq, Repr

end

/-- C++ control condition clause.

This is deliberately not just `ValExpr`.  Today the only constructor is a
boolean expression condition, but keeping a separate category makes the shared
condition lifecycle explicit for `if` and `while`: static typing, runtime
condition evaluation, replay, and post-state boundary reconstruction. -/
inductive CppCond where
  | expr : ValExpr → CppCond
  deriving DecidableEq, Repr

namespace CppCond

/-- Embed a value expression as the current expression-only condition form. -/
def ofValExpr (e : ValExpr) : CppCond :=
  .expr e

end CppCond

mutual
inductive CppStmt where
  | skip
  | exprStmt   : ValExpr → CppStmt
  | assign     : PlaceExpr → ValExpr → CppStmt
  | declareObj : CppType → Ident → Option ValExpr → CppStmt
  | declareRef : CppType → Ident → PlaceExpr → CppStmt
  | seq        : CppStmt → CppStmt → CppStmt
  | ite        : CppCond → CppStmt → CppStmt → CppStmt
  | whileStmt  : CppCond → CppStmt → CppStmt
  | block      : StmtBlock → CppStmt
  | breakStmt
  | continueStmt
  | returnStmt : Option ValExpr → CppStmt

inductive StmtBlock where
  | nil
  | cons : CppStmt → StmtBlock → StmtBlock
end

namespace StmtBlock

def ofList : List CppStmt → StmtBlock
  | [] => .nil
  | s :: ss => .cons s (ofList ss)

def toList : StmtBlock → List CppStmt
  | .nil => []
  | .cons s ss => s :: toList ss

def Mem (s : CppStmt) : StmtBlock → Prop
  | .nil => False
  | .cons t ts => s = t ∨ Mem s ts

@[simp] theorem mem_nil {s : CppStmt} : Mem s .nil ↔ False := by rfl
@[simp] theorem mem_cons {s t : CppStmt} {ss : StmtBlock} :
    Mem s (.cons t ss) ↔ s = t ∨ Mem s ss := by rfl

end StmtBlock


def CppStmt.blockOfList (xs : List CppStmt) : CppStmt :=
  .block (StmtBlock.ofList xs)

end Cpp3
