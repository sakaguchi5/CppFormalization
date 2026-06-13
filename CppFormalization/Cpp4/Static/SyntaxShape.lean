import CppFormalization.Cpp4.Static.Ident
import CppFormalization.Cpp4.Core.Syntax

/-!
# CppFormalization.Cpp4.Static.SyntaxShape

Typing-independent static shape predicates for Cpp4 surface syntax.

These predicates do not decide expression types or resource safety.  They only
record lexical/syntactic well-formedness facts that are visible before the
Typing, Boundary, Stability, and Soundness layers.
-/

namespace Cpp4

/-- Static shape of Cpp4 types.  Arrays are kept nonzero-sized at this layer. -/
inductive StaticTypeShape : CppType → Prop where
  | base {b : BaseType} : StaticTypeShape (.base b)
  | ptr {τ : CppType} : StaticTypeShape τ → StaticTypeShape (.ptr τ)
  | ref {τ : CppType} : StaticTypeShape τ → StaticTypeShape (.ref τ)
  | array {τ : CppType} {n : Nat} :
      StaticTypeShape τ → n > 0 → StaticTypeShape (.array τ n)

mutual

/-- Static shape of place expressions. -/
inductive StaticPlaceShape : PlaceExpr → Prop where
  | var {x : Ident} : StaticUserIdent x → StaticPlaceShape (.var x)
  | deref {e : ValExpr} : StaticValExprShape e → StaticPlaceShape (.deref e)

/-- Static shape of value expressions. -/
inductive StaticValExprShape : ValExpr → Prop where
  | litBool {b : Bool} : StaticValExprShape (.litBool b)
  | litInt {n : Int} : StaticValExprShape (.litInt n)
  | nullPtr : StaticValExprShape .nullPtr
  | load {p : PlaceExpr} : StaticPlaceShape p → StaticValExprShape (.load p)
  | addrOf {p : PlaceExpr} : StaticPlaceShape p → StaticValExprShape (.addrOf p)
  | add {lhs rhs : ValExpr} :
      StaticValExprShape lhs → StaticValExprShape rhs → StaticValExprShape (.add lhs rhs)
  | sub {lhs rhs : ValExpr} :
      StaticValExprShape lhs → StaticValExprShape rhs → StaticValExprShape (.sub lhs rhs)
  | mul {lhs rhs : ValExpr} :
      StaticValExprShape lhs → StaticValExprShape rhs → StaticValExprShape (.mul lhs rhs)
  | eq {lhs rhs : ValExpr} :
      StaticValExprShape lhs → StaticValExprShape rhs → StaticValExprShape (.eq lhs rhs)
  | lt {lhs rhs : ValExpr} :
      StaticValExprShape lhs → StaticValExprShape rhs → StaticValExprShape (.lt lhs rhs)
  | not {e : ValExpr} : StaticValExprShape e → StaticValExprShape (.not e)
  | call {f : FunctionName} {args : CallArgs} :
      StaticFunctionName f → StaticCallArgsShape args → StaticValExprShape (.call f args)

/-- Static shape of call-argument lists. -/
inductive StaticCallArgsShape : CallArgs → Prop where
  | nil : StaticCallArgsShape .nil
  | cons {e : ValExpr} {es : CallArgs} :
      StaticValExprShape e → StaticCallArgsShape es → StaticCallArgsShape (.cons e es)

end

/-- Static shape of boolean-like control conditions. -/
inductive StaticCondShape : CppCond → Prop where
  | expr {e : ValExpr} : StaticValExprShape e → StaticCondShape (.expr e)

/-- Static shape of switch conditions. -/
inductive StaticSwitchCondShape : CppSwitchCond → Prop where
  | expr {e : ValExpr} : StaticValExprShape e → StaticSwitchCondShape (.expr e)

/-- Static shape of object initializers. -/
inductive StaticInitShape : CppInit → Prop where
  | noInit : StaticInitShape .noInit
  | value {e : ValExpr} : StaticValExprShape e → StaticInitShape (.value e)

/-- Static shape of declarations. -/
inductive StaticDeclShape : CppDecl → Prop where
  | object {τ : CppType} {x : Ident} {init : CppInit} :
      StaticTypeShape τ → StaticUserIdent x → StaticInitShape init →
      StaticDeclShape (.object τ x init)
  | ref {τ : CppType} {x : Ident} {target : PlaceExpr} :
      StaticTypeShape τ → StaticUserIdent x → StaticPlaceShape target →
      StaticDeclShape (.ref τ x target)

/-- Static shape of return payloads. -/
inductive StaticReturnShape : CppReturn → Prop where
  | void : StaticReturnShape .void
  | value {e : ValExpr} : StaticValExprShape e → StaticReturnShape (.value e)

/-- Static shape of jump syntax.  Context validity remains a `ControlContext`/Typing
fact; this predicate only checks the contained payload. -/
inductive StaticJumpShape : CppJump → Prop where
  | breakStmt : StaticJumpShape .breakStmt
  | continueStmt : StaticJumpShape .continueStmt
  | returnStmt {r : CppReturn} : StaticReturnShape r → StaticJumpShape (.returnStmt r)

/-- Static shape of simple assignments. -/
inductive StaticAssignShape : CppAssign → Prop where
  | simple {p : PlaceExpr} {e : ValExpr} :
      StaticPlaceShape p → StaticValExprShape e → StaticAssignShape (.simple p e)

/-- Static shape of expression statements. -/
inductive StaticExprStmtShape : CppExprStmt → Prop where
  | discard {e : ValExpr} : StaticValExprShape e → StaticExprStmtShape (.discard e)

/-- Static shape of restricted `for` initializers. -/
inductive StaticForInitShape : CppForInit → Prop where
  | none : StaticForInitShape .none
  | expr {s : CppExprStmt} : StaticExprStmtShape s → StaticForInitShape (.expr s)
  | decl {d : CppDecl} : StaticDeclShape d → StaticForInitShape (.decl d)

/-- Static shape of restricted `for` iteration fragments. -/
inductive StaticForIterShape : CppForIter → Prop where
  | none : StaticForIterShape .none
  | expr {s : CppExprStmt} : StaticExprStmtShape s → StaticForIterShape (.expr s)
  | assign {a : CppAssign} : StaticAssignShape a → StaticForIterShape (.assign a)

/-- Static shape of normalized switch labels. -/
inductive StaticSwitchLabelShape : SwitchLabel → Prop where
  | caseInt {n : Int} : StaticSwitchLabelShape (.caseInt n)
  | defaultLabel : StaticSwitchLabelShape .defaultLabel

mutual

/-- Static shape of surface loops. -/
inductive StaticLoopShape : CppLoop → Prop where
  | whileLoop {c : CppCond} {body : CppStmt} :
      StaticCondShape c → StaticStmtShape body → StaticLoopShape (.whileLoop c body)
  | doWhileLoop {body : CppStmt} {c : CppCond} :
      StaticStmtShape body → StaticCondShape c → StaticLoopShape (.doWhileLoop body c)
  | forLoop {init : CppForInit} {cond : Option CppCond} {iter : CppForIter} {body : CppStmt} :
      StaticForInitShape init →
      (match cond with | none => True | some c => StaticCondShape c) →
      StaticForIterShape iter → StaticStmtShape body →
      StaticLoopShape (.forLoop init cond iter body)

/-- Static shape of surface statements. -/
inductive StaticStmtShape : CppStmt → Prop where
  | skip : StaticStmtShape .skip
  | exprStmt {s : CppExprStmt} : StaticExprStmtShape s → StaticStmtShape (.exprStmt s)
  | assign {a : CppAssign} : StaticAssignShape a → StaticStmtShape (.assign a)
  | decl {d : CppDecl} : StaticDeclShape d → StaticStmtShape (.decl d)
  | seq {s t : CppStmt} : StaticStmtShape s → StaticStmtShape t → StaticStmtShape (.seq s t)
  | ite {c : CppCond} {s t : CppStmt} :
      StaticCondShape c → StaticStmtShape s → StaticStmtShape t →
      StaticStmtShape (.ite c s t)
  | loop {l : CppLoop} : StaticLoopShape l → StaticStmtShape (.loop l)
  | switchStmt {c : CppSwitchCond} {arms : SwitchArmList} :
      StaticSwitchCondShape c → StaticSwitchArmListShape arms →
      StaticStmtShape (.switchStmt c arms)
  | block {b : StmtBlock} : StaticBlockShape b → StaticStmtShape (.block b)
  | jump {j : CppJump} : StaticJumpShape j → StaticStmtShape (.jump j)

/-- Static shape of surface statement blocks. -/
inductive StaticBlockShape : StmtBlock → Prop where
  | nil : StaticBlockShape .nil
  | cons {s : CppStmt} {rest : StmtBlock} :
      StaticStmtShape s → StaticBlockShape rest → StaticBlockShape (.cons s rest)

/-- Static shape of one surface switch arm. -/
inductive StaticSwitchArmShape : SwitchArm → Prop where
  | arm {label : SwitchLabel} {body : StmtBlock} :
      StaticSwitchLabelShape label → StaticBlockShape body →
      StaticSwitchArmShape (.arm label body)

/-- Static shape of surface switch-arm lists. -/
inductive StaticSwitchArmListShape : SwitchArmList → Prop where
  | nil : StaticSwitchArmListShape .nil
  | cons {arm : SwitchArm} {rest : SwitchArmList} :
      StaticSwitchArmShape arm → StaticSwitchArmListShape rest →
      StaticSwitchArmListShape (.cons arm rest)

end

end Cpp4
