import CppFormalization.Cpp3.Typing.Judgment.Stmt

namespace Cpp3
namespace Typing
namespace Judgment

/-!
# CppFormalization.Cpp3.Typing.Judgment.PrimitiveInversion

Shape-specific inversion helpers for primitive statement typing.

These lemmas are deliberately small: they recover the Micro primitive package and
its local components from the public `StmtTyping` judgment without exposing later
Effects/Boundary/Contracts assumptions.  They are the inverse direction of the
primitive smart constructors in `Reconstruction.lean`.
-/

namespace StmtTyping

/-- Invert a typed `skip` statement back to its primitive Micro package. -/
def primitive_of_skip
    {Γ Δ : TypeEnv} {k : ControlKind}
    (h : StmtTyping k Γ .skip Δ) :
    Micro.PrimitiveTyping Γ .skip k Δ := by
  cases h with
  | primitive hp => exact hp

/-- Invert a typed expression statement back to its primitive Micro package. -/
def primitive_of_exprStmt
    {Γ Δ : TypeEnv} {k : ControlKind} {es : CppExprStmt}
    (h : StmtTyping k Γ (.exprStmt es) Δ) :
    Micro.PrimitiveTyping Γ (.exprStmt es) k Δ := by
  cases h with
  | primitive hp => exact hp

/-- Invert a typed assignment statement back to its primitive Micro package. -/
def primitive_of_assign
    {Γ Δ : TypeEnv} {k : ControlKind} {a : CppAssign}
    (h : StmtTyping k Γ (.assign a) Δ) :
    Micro.PrimitiveTyping Γ (.assign a) k Δ := by
  cases h with
  | primitive hp => exact hp

/-- Invert a typed declaration statement back to its primitive Micro package. -/
def primitive_of_decl
    {Γ Δ : TypeEnv} {k : ControlKind} {d : CppDecl}
    (h : StmtTyping k Γ (.decl d) Δ) :
    Micro.PrimitiveTyping Γ (.decl d) k Δ := by
  cases h with
  | primitive hp => exact hp

/-- Invert a typed jump statement back to its primitive Micro package. -/
def primitive_of_jump
    {Γ Δ : TypeEnv} {k : ControlKind} {j : CppJump}
    (h : StmtTyping k Γ (.jump j) Δ) :
    Micro.PrimitiveTyping Γ (.jump j) k Δ := by
  cases h with
  | primitive hp => exact hp

/-- Extract expression-statement formation from an expression-statement typing. -/
def exprStmtFormation_of_exprStmt
    {Γ Δ : TypeEnv} {k : ControlKind} {es : CppExprStmt}
    (h : StmtTyping k Γ (.exprStmt es) Δ) :
    Micro.ExprStmtFormation Γ es := by
  have hp := primitive_of_exprStmt h
  cases hp.formation with
  | exprStmt hform => exact hform

/-- Extract expression-statement control effect from an expression-statement typing. -/
def exprStmtControl_of_exprStmt
    {Γ Δ : TypeEnv} {k : ControlKind} {es : CppExprStmt}
    (h : StmtTyping k Γ (.exprStmt es) Δ) :
    Micro.ExprStmtControlEffect es k := by
  have hp := primitive_of_exprStmt h
  cases hp.control with
  | exprStmt hctrl => exact hctrl

/-- Extract expression-statement environment effect from an expression-statement typing. -/
def exprStmtEnv_of_exprStmt
    {Γ Δ : TypeEnv} {k : ControlKind} {es : CppExprStmt}
    (h : StmtTyping k Γ (.exprStmt es) Δ) :
    Micro.ExprStmtEnvEffect Γ es Δ := by
  have hp := primitive_of_exprStmt h
  cases hp.env with
  | exprStmt henv => exact henv

/-- Extract assignment formation from an assignment typing. -/
def assignFormation_of_assign
    {Γ Δ : TypeEnv} {k : ControlKind} {a : CppAssign}
    (h : StmtTyping k Γ (.assign a) Δ) :
    Micro.AssignFormation Γ a := by
  have hp := primitive_of_assign h
  cases hp.formation with
  | assign hform => exact hform

/-- Extract assignment control effect from an assignment typing. -/
def assignControl_of_assign
    {Γ Δ : TypeEnv} {k : ControlKind} {a : CppAssign}
    (h : StmtTyping k Γ (.assign a) Δ) :
    Micro.AssignControlEffect a k := by
  have hp := primitive_of_assign h
  cases hp.control with
  | assign hctrl => exact hctrl

/-- Extract assignment environment effect from an assignment typing. -/
def assignEnv_of_assign
    {Γ Δ : TypeEnv} {k : ControlKind} {a : CppAssign}
    (h : StmtTyping k Γ (.assign a) Δ) :
    Micro.AssignEnvEffect Γ a Δ := by
  have hp := primitive_of_assign h
  cases hp.env with
  | assign henv => exact henv

/-- Extract declaration formation from a declaration-statement typing. -/
def declFormation_of_decl
    {Γ Δ : TypeEnv} {k : ControlKind} {d : CppDecl}
    (h : StmtTyping k Γ (.decl d) Δ) :
    Micro.DeclFormation Γ d := by
  have hp := primitive_of_decl h
  cases hp.formation with
  | decl hform => exact hform

/-- Extract declaration environment effect from a declaration-statement typing. -/
def declEnv_of_decl
    {Γ Δ : TypeEnv} {k : ControlKind} {d : CppDecl}
    (h : StmtTyping k Γ (.decl d) Δ) :
    Micro.DeclEnvEffect Γ d Δ := by
  have hp := primitive_of_decl h
  cases hp.env with
  | decl henv => exact henv

/-- Extract jump formation from a jump-statement typing. -/
def jumpFormation_of_jump
    {Γ Δ : TypeEnv} {k : ControlKind} {j : CppJump}
    (h : StmtTyping k Γ (.jump j) Δ) :
    Micro.JumpFormation Γ j := by
  have hp := primitive_of_jump h
  cases hp.formation with
  | jump hform => exact hform

/-- Extract jump control effect from a jump-statement typing. -/
def jumpControl_of_jump
    {Γ Δ : TypeEnv} {k : ControlKind} {j : CppJump}
    (h : StmtTyping k Γ (.jump j) Δ) :
    Micro.JumpControlEffect j k := by
  have hp := primitive_of_jump h
  cases hp.control with
  | jump hctrl => exact hctrl

/-- Extract jump environment effect from a jump-statement typing. -/
def jumpEnv_of_jump
    {Γ Δ : TypeEnv} {k : ControlKind} {j : CppJump}
    (h : StmtTyping k Γ (.jump j) Δ) :
    Micro.JumpEnvEffect Γ j Δ := by
  have hp := primitive_of_jump h
  cases hp.env with
  | jump henv => exact henv

end StmtTyping

end Judgment
end Typing
end Cpp3
