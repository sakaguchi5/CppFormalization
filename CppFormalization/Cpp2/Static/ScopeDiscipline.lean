import CppFormalization.Cpp2.Core.Syntax

/-!
`break` / `continue` scope discipline.
-/

namespace Cpp

mutual

def BreakWellScopedAt : Nat → CppStmt → Prop
  | _d, .skip => True
  | _d, .exprStmt _ => True
  | _d, .assign _ _ => True
  | _d, .declareObj _ _ _ => True
  | _d, .declareRef _ _ _ => True
  | d, .seq s t => BreakWellScopedAt d s ∧ BreakWellScopedAt d t
  | d, .ite _ s t => BreakWellScopedAt d s ∧ BreakWellScopedAt d t
  | d, .whileStmt _ b => BreakWellScopedAt (d + 1) b
  | d, .block ss => BreakWellScopedBlockAt d ss
  | 0, .breakStmt => False
  | Nat.succ _, .breakStmt => True
  | _d, .continueStmt => True
  | _d, .returnStmt _ => True


def BreakWellScopedBlockAt : Nat → StmtBlock → Prop
  | _d, .nil => True
  | d, .cons s ss => BreakWellScopedAt d s ∧ BreakWellScopedBlockAt d ss

end

mutual

def ContinueWellScopedAt : Nat → CppStmt → Prop
  | _d, .skip => True
  | _d, .exprStmt _ => True
  | _d, .assign _ _ => True
  | _d, .declareObj _ _ _ => True
  | _d, .declareRef _ _ _ => True
  | d, .seq s t => ContinueWellScopedAt d s ∧ ContinueWellScopedAt d t
  | d, .ite _ s t => ContinueWellScopedAt d s ∧ ContinueWellScopedAt d t
  | d, .whileStmt _ b => ContinueWellScopedAt (d + 1) b
  | d, .block ss => ContinueWellScopedBlockAt d ss
  | _d, .breakStmt => True
  | 0, .continueStmt => False
  | Nat.succ _, .continueStmt => True
  | _d, .returnStmt _ => True


def ContinueWellScopedBlockAt : Nat → StmtBlock → Prop
  | _d, .nil => True
  | d, .cons s ss => ContinueWellScopedAt d s ∧ ContinueWellScopedBlockAt d ss

end

abbrev BreakWellScoped (st : CppStmt) : Prop := BreakWellScopedAt 0 st
abbrev ContinueWellScoped (st : CppStmt) : Prop := ContinueWellScopedAt 0 st

end Cpp
