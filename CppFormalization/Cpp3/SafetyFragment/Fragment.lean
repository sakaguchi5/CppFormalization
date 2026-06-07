import CppFormalization.Cpp3.SafetyFragment.Lifetime
import CppFormalization.Cpp3.SafetyFragment.Deref
import CppFormalization.Cpp3.SafetyFragment.Footprint
import CppFormalization.Cpp3.SafetyFragment.Loop
import CppFormalization.Cpp3.SafetyFragment.External

/-!
# CppFormalization.Cpp3.SafetyFragment.Fragment

Composite safe-fragment packages for expressions, statements, blocks, and
function bodies.

These structures deliberately do not prove progress, preservation, or no stuck.
They only collect the C++-facing obligations that later layers consume.
-/

namespace Cpp3
namespace SafetyFragment

/-- Safe-fragment package for a value expression. -/
structure ValSafetyFragment (Γ : TypeEnv) (e : ValExpr) : Type where
  effect : Effects.ValEffect Γ e
  derefSafe : Prop
  derefEvidence : Effects.ValEffect.derefUse effect → Contracts.Requires derefSafe

/-- Safe-fragment package for a condition. -/
structure CondSafetyFragment (Γ Γc : TypeEnv) (cond : CppCond) : Type where
  effect : Effects.CondEffect Γ Γc cond
  derefSafe : CondDerefSafety Γ Γc cond

/-- Safe-fragment package for an assignment. -/
structure AssignSafetyFragment (Γ : TypeEnv) (a : CppAssign) : Type where
  effect : Effects.AssignEffect Γ a
  writableTarget : WritableTargetAvailable Γ a
  noInvalidatesLaterUse : Prop
  noInvalidatesLaterUseEvidence : Contracts.Requires noInvalidatesLaterUse

/-- Safe-fragment package for a declaration. -/
structure DeclSafetyFragment (Γ Δ : TypeEnv) (d : CppDecl) : Type where
  effect : Effects.DeclEffect Γ Δ d
  noInvalidatesLaterUse : Prop
  noInvalidatesLaterUseEvidence : Contracts.Requires noInvalidatesLaterUse

/-- Safe-fragment package for a statement. -/
structure StmtSafetyFragment (Γ : TypeEnv) (st : CppStmt) : Type where
  effect : Effects.StmtEffect Γ st
  lifetimeSafe : Prop
  lifetimeEvidence : Contracts.Requires lifetimeSafe
  derefSafe : Prop
  derefEvidence : Contracts.Requires derefSafe
  footprintSafe : Prop
  footprintEvidence : Contracts.Requires footprintSafe

/-- Safe-fragment package for a block body. -/
structure BlockSafetyFragment (Γ : TypeEnv) (body : StmtBlock) : Type where
  effect : Effects.BlockEffect Γ body
  lifetimeSafe : Prop
  lifetimeEvidence : Contracts.Requires lifetimeSafe
  derefSafe : Prop
  derefEvidence : Contracts.Requires derefSafe
  footprintSafe : Prop
  footprintEvidence : Contracts.Requires footprintSafe

/-- Safe-fragment package for a function body.

Top-level break/continue exclusion is not asserted here; that belongs to
Semantics/Kernel classification and later Soundness.  This package only says the
body lies inside the intended safe C++ fragment. -/
structure FunctionBodySafetyFragment (Γ : TypeEnv) (body : CppStmt) : Type where
  effect : Effects.FunctionBodyEffect Γ body
  stmtSafety : StmtSafetyFragment Γ body

end SafetyFragment
end Cpp3
