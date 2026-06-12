import CppFormalization.Cpp4.Core.Control

/-!
# CppFormalization.Cpp4.Core.Syntax

Cpp4 surface Core syntax.

This is the second layer of the Core design: it keeps C++-shaped structured
constructs such as loops and switches.  `Core.ControlPlan` then expands these
constructs into smaller structured-control atoms for semantics and soundness.

Function call is included from the beginning as a value expression; call
statements are discarded call expressions.
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

/-- Boolean-like C++ control condition used by if/while/do/for. -/
inductive CppCond where
  | expr : ValExpr → CppCond
  deriving DecidableEq, Repr

/-- Switch condition.  This is intentionally separate from `CppCond` because C++
switch conditions are integral-like rather than merely boolean-like. -/
inductive CppSwitchCond where
  | expr : ValExpr → CppSwitchCond
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

/-- Restricted for-initializer surface for the initial Cpp4 fragment. -/
inductive CppForInit where
  | none
  | expr : CppExprStmt → CppForInit
  | decl : CppDecl → CppForInit
  deriving DecidableEq, Repr

/-- Restricted iteration-expression surface.  It deliberately cannot contain
`break`, `continue`, or `return`. -/
inductive CppForIter where
  | none
  | expr : CppExprStmt → CppForIter
  | assign : CppAssign → CppForIter
  deriving DecidableEq, Repr

/-- Normalized switch labels.  Full source-level constant-expression checking is
a Static/Source responsibility; Core starts with integer labels plus default. -/
inductive SwitchLabel where
  | caseInt : Int → SwitchLabel
  | defaultLabel : SwitchLabel
  deriving DecidableEq, Repr

mutual

inductive CppLoop where
  | whileLoop : CppCond → CppStmt → CppLoop
  | doWhileLoop : CppStmt → CppCond → CppLoop
  | forLoop : CppForInit → Option CppCond → CppForIter → CppStmt → CppLoop
  deriving DecidableEq, Repr

inductive CppStmt where
  | skip
  | exprStmt : CppExprStmt → CppStmt
  | assign : CppAssign → CppStmt
  | decl : CppDecl → CppStmt
  | seq : CppStmt → CppStmt → CppStmt
  | ite : CppCond → CppStmt → CppStmt → CppStmt
  | loop : CppLoop → CppStmt
  | switchStmt : CppSwitchCond → SwitchArmList → CppStmt
  | block : StmtBlock → CppStmt
  | jump : CppJump → CppStmt
  deriving DecidableEq, Repr

inductive StmtBlock where
  | nil
  | cons : CppStmt → StmtBlock → StmtBlock
  deriving DecidableEq, Repr

inductive SwitchArm where
  | arm : SwitchLabel → StmtBlock → SwitchArm
  deriving DecidableEq, Repr

inductive SwitchArmList where
  | nil
  | cons : SwitchArm → SwitchArmList → SwitchArmList
  deriving DecidableEq, Repr

end

namespace CppStmt

/-- Compatibility constructor for the old single-loop surface. -/
def whileStmt (c : CppCond) (body : CppStmt) : CppStmt :=
  .loop (.whileLoop c body)

/-- Smart constructor for do-while. -/
def doWhileStmt (body : CppStmt) (c : CppCond) : CppStmt :=
  .loop (.doWhileLoop body c)

/-- Smart constructor for for loops. -/
def forStmt (init : CppForInit) (cond : Option CppCond)
    (iter : CppForIter) (body : CppStmt) : CppStmt :=
  .loop (.forLoop init cond iter body)

end CppStmt

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

namespace SwitchArm

def label : SwitchArm → SwitchLabel
  | .arm l _ => l

def body : SwitchArm → StmtBlock
  | .arm _ b => b

end SwitchArm

namespace SwitchArmList

def toList : SwitchArmList → List SwitchArm
  | .nil => []
  | .cons arm rest => arm :: rest.toList

def length : SwitchArmList → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

end SwitchArmList

namespace CppStmt

def switchCond? : CppStmt → Option CppSwitchCond
  | .switchStmt c _ => some c
  | _ => none

def switchArms? : CppStmt → Option SwitchArmList
  | .switchStmt _ arms => some arms
  | _ => none

end CppStmt

end Cpp4
