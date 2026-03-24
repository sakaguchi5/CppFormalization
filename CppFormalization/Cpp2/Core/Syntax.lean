import CppFormalization.Cpp2.Core.Types

/-!
Expression and statement syntax, plus the concrete big-step fragment marker.
-/

namespace Cpp

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

mutual
inductive CppStmt where
  | skip
  | exprStmt   : ValExpr → CppStmt
  | assign     : PlaceExpr → ValExpr → CppStmt
  | declareObj : CppType → Ident → Option ValExpr → CppStmt
  | declareRef : CppType → Ident → PlaceExpr → CppStmt
  | seq        : CppStmt → CppStmt → CppStmt
  | ite        : ValExpr → CppStmt → CppStmt → CppStmt
  | whileStmt  : ValExpr → CppStmt → CppStmt
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

mutual

def InBigStepFragment : CppStmt → Prop
  | .skip => True
  | .exprStmt _ => True
  | .assign _ _ => True
  | .declareObj _ _ _ => True
  | .declareRef _ _ _ => True
  | .seq s t => InBigStepFragment s ∧ InBigStepFragment t
  | .ite _ s t => InBigStepFragment s ∧ InBigStepFragment t
  | .whileStmt _ body => InBigStepFragment body
  | .block ss => InBigStepBlockFragment ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt _ => True

def InBigStepBlockFragment : StmtBlock → Prop
  | .nil => True
  | .cons s ss => InBigStepFragment s ∧ InBigStepBlockFragment ss

end

def CoreBigStepFragment (st : CppStmt) : Prop :=
  InBigStepFragment st

end Cpp
