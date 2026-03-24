import CppFormalization.Cpp2.Core.Syntax

/-!
Pure syntactic well-formedness.
-/

namespace Cpp

mutual

def WellFormedPlace : PlaceExpr → Prop
  | .var _ => True
  | .deref e => WellFormedValue e


def WellFormedValue : ValExpr → Prop
  | .litBool _ => True
  | .litInt _ => True
  | .load p => WellFormedPlace p
  | .addrOf p => WellFormedPlace p
  | .add e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .sub e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .mul e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .eq e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .lt e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .not e => WellFormedValue e

end

mutual

def WellFormedStmt : CppStmt → Prop
  | .skip => True
  | .exprStmt e => WellFormedValue e
  | .assign p e => WellFormedPlace p ∧ WellFormedValue e
  | .declareObj _ _ none => True
  | .declareObj _ _ (some e) => WellFormedValue e
  | .declareRef _ _ p => WellFormedPlace p
  | .seq s t => WellFormedStmt s ∧ WellFormedStmt t
  | .ite c s t => WellFormedValue c ∧ WellFormedStmt s ∧ WellFormedStmt t
  | .whileStmt c b => WellFormedValue c ∧ WellFormedStmt b
  | .block ss => WellFormedBlock ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt none => True
  | .returnStmt (some e) => WellFormedValue e


def WellFormedBlock : StmtBlock → Prop
  | .nil => True
  | .cons s ss => WellFormedStmt s ∧ WellFormedBlock ss

end

end Cpp
