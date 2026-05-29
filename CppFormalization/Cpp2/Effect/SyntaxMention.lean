import CppFormalization.Cpp2.Language.Syntax

namespace Cpp

/-!
# CppFormalization.Cpp2.Effects.SyntaxMention

Axiom-free syntactic old-name vocabulary for the effect layer.

This deliberately duplicates no `Closure.Internal` dependency.  The old-name
transport route can later consume these predicates from `Effects` instead of
importing the old refined Closure surface.
-/

mutual

/-- A place expression does not mention a given freshly introduced identifier. -/
inductive EffectPlaceDoesNotMentionIdent : Ident → PlaceExpr → Prop where
  | var {fresh y : Ident} :
      y ≠ fresh →
      EffectPlaceDoesNotMentionIdent fresh (.var y)
  | deref {fresh : Ident} {e : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e →
      EffectPlaceDoesNotMentionIdent fresh (.deref e)

/-- A value expression does not mention a given freshly introduced identifier. -/
inductive EffectExprDoesNotMentionIdent : Ident → ValExpr → Prop where
  | litBool {fresh : Ident} {b : Bool} :
      EffectExprDoesNotMentionIdent fresh (.litBool b)
  | litInt {fresh : Ident} {n : Int} :
      EffectExprDoesNotMentionIdent fresh (.litInt n)
  | load {fresh : Ident} {p : PlaceExpr} :
      EffectPlaceDoesNotMentionIdent fresh p →
      EffectExprDoesNotMentionIdent fresh (.load p)
  | addrOf {fresh : Ident} {p : PlaceExpr} :
      EffectPlaceDoesNotMentionIdent fresh p →
      EffectExprDoesNotMentionIdent fresh (.addrOf p)
  | add {fresh : Ident} {e₁ e₂ : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e₁ →
      EffectExprDoesNotMentionIdent fresh e₂ →
      EffectExprDoesNotMentionIdent fresh (.add e₁ e₂)
  | sub {fresh : Ident} {e₁ e₂ : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e₁ →
      EffectExprDoesNotMentionIdent fresh e₂ →
      EffectExprDoesNotMentionIdent fresh (.sub e₁ e₂)
  | mul {fresh : Ident} {e₁ e₂ : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e₁ →
      EffectExprDoesNotMentionIdent fresh e₂ →
      EffectExprDoesNotMentionIdent fresh (.mul e₁ e₂)
  | eq {fresh : Ident} {e₁ e₂ : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e₁ →
      EffectExprDoesNotMentionIdent fresh e₂ →
      EffectExprDoesNotMentionIdent fresh (.eq e₁ e₂)
  | lt {fresh : Ident} {e₁ e₂ : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e₁ →
      EffectExprDoesNotMentionIdent fresh e₂ →
      EffectExprDoesNotMentionIdent fresh (.lt e₁ e₂)
  | not {fresh : Ident} {e : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e →
      EffectExprDoesNotMentionIdent fresh (.not e)

/-- A statement does not mention a given freshly introduced identifier. -/
inductive EffectStmtDoesNotMentionIdent : Ident → CppStmt → Prop where
  | skip {fresh : Ident} :
      EffectStmtDoesNotMentionIdent fresh .skip
  | exprStmt {fresh : Ident} {e : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e →
      EffectStmtDoesNotMentionIdent fresh (.exprStmt e)
  | assign {fresh : Ident} {p : PlaceExpr} {e : ValExpr} :
      EffectPlaceDoesNotMentionIdent fresh p →
      EffectExprDoesNotMentionIdent fresh e →
      EffectStmtDoesNotMentionIdent fresh (.assign p e)
  | declareObjNone {fresh y : Ident} {τ : CppType} :
      y ≠ fresh →
      EffectStmtDoesNotMentionIdent fresh (.declareObj τ y none)
  | declareObjSome {fresh y : Ident} {τ : CppType} {e : ValExpr} :
      y ≠ fresh →
      EffectExprDoesNotMentionIdent fresh e →
      EffectStmtDoesNotMentionIdent fresh (.declareObj τ y (some e))
  | declareRef {fresh y : Ident} {τ : CppType} {p : PlaceExpr} :
      y ≠ fresh →
      EffectPlaceDoesNotMentionIdent fresh p →
      EffectStmtDoesNotMentionIdent fresh (.declareRef τ y p)
  | seq {fresh : Ident} {s t : CppStmt} :
      EffectStmtDoesNotMentionIdent fresh s →
      EffectStmtDoesNotMentionIdent fresh t →
      EffectStmtDoesNotMentionIdent fresh (.seq s t)
  | ite {fresh : Ident} {c : ValExpr} {s t : CppStmt} :
      EffectExprDoesNotMentionIdent fresh c →
      EffectStmtDoesNotMentionIdent fresh s →
      EffectStmtDoesNotMentionIdent fresh t →
      EffectStmtDoesNotMentionIdent fresh (.ite c s t)
  | whileStmt {fresh : Ident} {c : ValExpr} {body : CppStmt} :
      EffectExprDoesNotMentionIdent fresh c →
      EffectStmtDoesNotMentionIdent fresh body →
      EffectStmtDoesNotMentionIdent fresh (.whileStmt c body)
  | block {fresh : Ident} {ss : StmtBlock} :
      EffectBlockDoesNotMentionIdent fresh ss →
      EffectStmtDoesNotMentionIdent fresh (.block ss)
  | breakStmt {fresh : Ident} :
      EffectStmtDoesNotMentionIdent fresh .breakStmt
  | continueStmt {fresh : Ident} :
      EffectStmtDoesNotMentionIdent fresh .continueStmt
  | returnNone {fresh : Ident} :
      EffectStmtDoesNotMentionIdent fresh (.returnStmt none)
  | returnSome {fresh : Ident} {e : ValExpr} :
      EffectExprDoesNotMentionIdent fresh e →
      EffectStmtDoesNotMentionIdent fresh (.returnStmt (some e))

/-- A block does not mention a given freshly introduced identifier. -/
inductive EffectBlockDoesNotMentionIdent : Ident → StmtBlock → Prop where
  | nil {fresh : Ident} :
      EffectBlockDoesNotMentionIdent fresh .nil
  | cons {fresh : Ident} {s : CppStmt} {ss : StmtBlock} :
      EffectStmtDoesNotMentionIdent fresh s →
      EffectBlockDoesNotMentionIdent fresh ss →
      EffectBlockDoesNotMentionIdent fresh (.cons s ss)

end

end Cpp
