import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

mutual

inductive NoDeclareObjStmt : CppStmt → Prop where
  | skip :
      NoDeclareObjStmt .skip
  | exprStmt {e : ValExpr} :
      NoDeclareObjStmt (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} :
      NoDeclareObjStmt (.assign p e)
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} :
      NoDeclareObjStmt (.declareRef τ x p)
  | seq {s t : CppStmt} :
      NoDeclareObjStmt s →
      NoDeclareObjStmt t →
      NoDeclareObjStmt (.seq s t)
  | ite {c : ValExpr} {s t : CppStmt} :
      NoDeclareObjStmt s →
      NoDeclareObjStmt t →
      NoDeclareObjStmt (.ite c s t)
  | whileStmt {c : ValExpr} {body : CppStmt} :
      NoDeclareObjStmt body →
      NoDeclareObjStmt (.whileStmt c body)
  | block {ss : StmtBlock} :
      NoDeclareObjBlock ss →
      NoDeclareObjStmt (.block ss)
  | breakStmt :
      NoDeclareObjStmt .breakStmt
  | continueStmt :
      NoDeclareObjStmt .continueStmt
  | returnStmt {oe : Option ValExpr} :
      NoDeclareObjStmt (.returnStmt oe)

inductive NoDeclareObjBlock : StmtBlock → Prop where
  | nil :
      NoDeclareObjBlock .nil
  | cons {s : CppStmt} {ss : StmtBlock} :
      NoDeclareObjStmt s →
      NoDeclareObjBlock ss →
      NoDeclareObjBlock (.cons s ss)

end


end Cpp
