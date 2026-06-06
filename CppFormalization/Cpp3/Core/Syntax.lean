import CppFormalization.Cpp3.Core.Types

/-!
Expression, condition, declaration, initializer, and statement syntax.

`CppCond` is a separate syntactic category for C++ control conditions.  The
current core only supports expression conditions, but `if` and `while` consume
conditions rather than raw value expressions so typing/effects/replay/boundary
facts can be stated once for both constructs.

`CppInit` and `CppDecl` are separate syntactic categories for C++ declarations.
A declaration is not just an ordinary statement shape: it has its own initializer
payload, type-environment effect, runtime allocation/binding effect, and lifetime
boundary.  The statement layer embeds declarations through `CppStmt.decl`.
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

/-- C++ object initializer payload.

The current core distinguishes `noInit` declarations from value-expression
initializers.  This is kept as a separate category instead of `Option ValExpr`
so initializer typing/evaluation/storage/lifetime facts can be named directly. -/
inductive CppInit where
  | noInit : CppInit
  | value : ValExpr → CppInit
  deriving DecidableEq, Repr

/-- C++ declaration syntax.

Declarations are separated from statements because they have their own static
environment effect and runtime binding/allocation lifecycle. -/
inductive CppDecl where
  | object : CppType → Ident → CppInit → CppDecl
  | ref    : CppType → Ident → PlaceExpr → CppDecl
  deriving DecidableEq, Repr

mutual
inductive CppStmt where
  | skip
  | exprStmt   : ValExpr → CppStmt
  | assign     : PlaceExpr → ValExpr → CppStmt
  | decl       : CppDecl → CppStmt
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
