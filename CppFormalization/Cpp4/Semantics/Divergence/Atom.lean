import CppFormalization.Cpp4.Semantics.Divergence.Call
import CppFormalization.Cpp4.Semantics.Kernel.Atom

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Atom

Divergence vocabulary for primitive atom components.
-/

namespace Cpp4

inductive DivergesInit (χ : KernelContext) : State → CppInit → Prop where
  | value {σ : State} {e : ValExpr} :
      DivergesValue χ σ e →
      DivergesInit χ σ (.value e)

inductive DivergesDecl (χ : KernelContext) : State → CppDecl → Prop where
  | objectInit {σ : State} {τ : CppType} {x : Ident} {init : CppInit} :
      DivergesInit χ σ init →
      DivergesDecl χ σ (.object τ x init)
  | refPlace {σ : State} {τ : CppType} {x : Ident} {p : PlaceExpr} :
      DivergesPlace χ σ p →
      DivergesDecl χ σ (.ref τ x p)

inductive DivergesExprStmt (χ : KernelContext) : State → CppExprStmt → Prop where
  | discard {σ : State} {e : ValExpr} :
      DivergesValue χ σ e →
      DivergesExprStmt χ σ (.discard e)

inductive DivergesAssign (χ : KernelContext) : State → CppAssign → Prop where
  | place {σ : State} {p : PlaceExpr} {e : ValExpr} :
      DivergesPlace χ σ p →
      DivergesAssign χ σ (.simple p e)
  | value {σ σp : State} {p : PlaceExpr} {e : ValExpr} {a : Address} :
      BigStepPlace χ σ p a σp →
      DivergesValue χ σp e →
      DivergesAssign χ σ (.simple p e)

inductive DivergesForInit (χ : KernelContext) : State → CppForInit → Prop where
  | expr {σ : State} {s : CppExprStmt} :
      DivergesExprStmt χ σ s →
      DivergesForInit χ σ (.expr s)
  | decl {σ : State} {d : CppDecl} :
      DivergesDecl χ σ d →
      DivergesForInit χ σ (.decl d)

inductive DivergesForIter (χ : KernelContext) : State → CppForIter → Prop where
  | expr {σ : State} {s : CppExprStmt} :
      DivergesExprStmt χ σ s →
      DivergesForIter χ σ (.expr s)
  | assign {σ : State} {a : CppAssign} :
      DivergesAssign χ σ a →
      DivergesForIter χ σ (.assign a)

inductive DivergesAtom (χ : KernelContext) : State → ControlAtom → Prop where
  | exprStmt {σ : State} {s : CppExprStmt} :
      DivergesExprStmt χ σ s →
      DivergesAtom χ σ (.exprStmt s)
  | assign {σ : State} {a : CppAssign} :
      DivergesAssign χ σ a →
      DivergesAtom χ σ (.assign a)
  | decl {σ : State} {d : CppDecl} :
      DivergesDecl χ σ d →
      DivergesAtom χ σ (.decl d)
  | returnValue {σ : State} {e : ValExpr} :
      DivergesValue χ σ e →
      DivergesAtom χ σ (.jump (.returnStmt (.value e)))

end Cpp4
