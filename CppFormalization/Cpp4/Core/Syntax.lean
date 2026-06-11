import CppFormalization.Cpp4.Core.Control

/-!
# CppFormalization.Cpp4.Core.Syntax

Cpp4 syntax.  Function call is included from the beginning as a value expression;
call statements are discarded call expressions.
-/

namespace Cpp4

mutual

inductive PlaceExpr where
  | var : Ident → PlaceExpr
  | deref : ValExpr → PlaceExpr
  deriving DecidableEq, Repr

inductive ValExpr where
  | litBool : Bool → ValExpr
  | litInt : Int → ValExpr
  | nullPtr : ValExpr
  | load : PlaceExpr → ValExpr
  | addrOf : PlaceExpr → ValExpr
  | add : ValExpr → ValExpr → ValExpr
  | sub : ValExpr → ValExpr → ValExpr
  | mul : ValExpr → ValExpr → ValExpr
  | eq : ValExpr → ValExpr → ValExpr
  | lt : ValExpr → ValExpr → ValExpr
  | not : ValExpr → ValExpr
  | call : FunctionName → CallArgs → ValExpr
  deriving DecidableEq, Repr

inductive CallArgs where
  | nil : CallArgs
  | cons : ValExpr → CallArgs → CallArgs
  deriving DecidableEq, Repr

end

/-- C++ control condition category. -/
inductive CppCond where
  | expr : ValExpr → CppCond
  deriving DecidableEq, Repr

/-- Object initializer payload. -/
inductive CppInit where
  | noInit
  | value : ValExpr → CppInit
  deriving DecidableEq, Repr

/-- Declaration syntax. -/
inductive CppDecl where
  | object : CppType → Ident → CppInit → CppDecl
  | ref : CppType → Ident → PlaceExpr → CppDecl
  deriving DecidableEq, Repr

/-- Return payload. -/
inductive CppReturn where
  | void
  | value : ValExpr → CppReturn
  deriving DecidableEq, Repr

/-- Non-local control-transfer syntax. -/
inductive CppJump where
  | breakStmt
  | continueStmt
  | returnStmt : CppReturn → CppJump
  deriving DecidableEq, Repr

/-- Simple assignment. -/
inductive CppAssign where
  | simple : PlaceExpr → ValExpr → CppAssign
  deriving DecidableEq, Repr

/-- Expression statement; calls are represented as discarded value expressions. -/
inductive CppExprStmt where
  | discard : ValExpr → CppExprStmt
  deriving DecidableEq, Repr

mutual

inductive CppStmt where
  | skip
  | exprStmt : CppExprStmt → CppStmt
  | assign : CppAssign → CppStmt
  | decl : CppDecl → CppStmt
  | seq : CppStmt → CppStmt → CppStmt
  | ite : CppCond → CppStmt → CppStmt → CppStmt
  | whileStmt : CppCond → CppStmt → CppStmt
  | block : StmtBlock → CppStmt
  | jump : CppJump → CppStmt
  deriving DecidableEq, Repr

inductive StmtBlock where
  | nil
  | cons : CppStmt → StmtBlock → StmtBlock
  deriving DecidableEq, Repr

end

namespace StmtBlock

def ofList : List CppStmt → StmtBlock
  | [] => .nil
  | s :: ss => .cons s (ofList ss)

def toList : StmtBlock → List CppStmt
  | .nil => []
  | .cons s ss => s :: toList ss

end StmtBlock

namespace CallArgs

def ofList : List ValExpr → CallArgs
  | [] => .nil
  | e :: es => .cons e (ofList es)

def toList : CallArgs → List ValExpr
  | .nil => []
  | .cons e es => e :: toList es

def length : CallArgs → Nat
  | .nil => 0
  | .cons _ es => es.length + 1

end CallArgs

end Cpp4
