import CppFormalization.Cpp3.Effects.Syntax
import CppFormalization.Cpp3.Static.Scope

/-!
# CppFormalization.Cpp3.Effects.Primitive

Primitive effect surfaces.

These packages connect static formation/environment surfaces to syntax-directed
read/write/bind observations.  They do not contain runtime readiness and do not
prove preservation of any later boundary.
-/

namespace Cpp3
namespace Effects

/-- Effect surface for a place expression. -/
structure PlaceEffect (Γ : TypeEnv) (p : PlaceExpr) : Type where
  formed : Static.StaticPlaceFormed p

namespace PlaceEffect

def readsName {Γ : TypeEnv} {p : PlaceExpr} (_ : PlaceEffect Γ p) : NameSet :=
  fun x => PlaceReadsName p x

def derefUse {Γ : TypeEnv} {p : PlaceExpr} (_ : PlaceEffect Γ p) : Prop :=
  PlaceDerefUse p

end PlaceEffect

/-- Effect surface for a value expression. -/
structure ValEffect (Γ : TypeEnv) (e : ValExpr) : Type where
  formed : Static.StaticValFormed e

namespace ValEffect

def readsName {Γ : TypeEnv} {e : ValExpr} (_ : ValEffect Γ e) : NameSet :=
  fun x => ValReadsName e x

def derefUse {Γ : TypeEnv} {e : ValExpr} (_ : ValEffect Γ e) : Prop :=
  ValDerefUse e

end ValEffect

/-- Effect surface for a condition. -/
structure CondEffect (Γ Γc : TypeEnv) (cond : CppCond) : Type where
  formed : Static.StaticCondFormed cond

namespace CondEffect

def readsName {Γ Γc : TypeEnv} {cond : CppCond}
    (_ : CondEffect Γ Γc cond) : NameSet :=
  fun x => CondReadsName cond x

def derefUse {Γ Γc : TypeEnv} {cond : CppCond}
    (_ : CondEffect Γ Γc cond) : Prop :=
  CondDerefUse cond

end CondEffect

/-- Effect surface for an initializer. -/
structure InitEffect (Γ : TypeEnv) (init : CppInit) : Type where
  formed : Static.StaticInitFormed init

namespace InitEffect

def readsName {Γ : TypeEnv} {init : CppInit}
    (_ : InitEffect Γ init) : NameSet :=
  fun x => InitReadsName init x

def derefUse {Γ : TypeEnv} {init : CppInit}
    (_ : InitEffect Γ init) : Prop :=
  InitDerefUse init

end InitEffect

/-- Effect surface for an assignment. -/
structure AssignEffect (Γ : TypeEnv) (a : CppAssign) : Type where
  formed : Static.StaticAssignFormed a

namespace AssignEffect

def readsName {Γ : TypeEnv} {a : CppAssign}
    (_ : AssignEffect Γ a) : NameSet :=
  fun x => AssignReadsName a x

def writesDirectName {Γ : TypeEnv} {a : CppAssign}
    (_ : AssignEffect Γ a) : NameSet :=
  fun x => AssignWritesDirectName a x

end AssignEffect

/-- Effect surface for a declaration.

The static environment effect is included because declarations are the primitive
place where syntax changes the static environment. -/
structure DeclEffect (Γ Δ : TypeEnv) (d : CppDecl) : Type where
  formed : Static.StaticDeclFormed d
  env : Static.StaticDeclEnvEffect Γ d Δ

namespace DeclEffect

def readsName {Γ Δ : TypeEnv} {d : CppDecl}
    (_ : DeclEffect Γ Δ d) : NameSet :=
  fun x => DeclReadsName d x

def bindsName {Γ Δ : TypeEnv} {d : CppDecl}
    (_ : DeclEffect Γ Δ d) : NameSet :=
  fun x => DeclBindsName d x

end DeclEffect

/-- Effect surface for an expression statement. -/
structure ExprStmtEffect (Γ : TypeEnv) (e : CppExprStmt) : Type where
  formed : Static.StaticExprStmtFormed e

namespace ExprStmtEffect

def readsName {Γ : TypeEnv} {e : CppExprStmt}
    (_ : ExprStmtEffect Γ e) : NameSet :=
  fun x => ExprStmtReadsName e x

end ExprStmtEffect

/-- Effect surface for a return payload. -/
structure ReturnEffect (Γ : TypeEnv) (r : CppReturn) : Type where
  formed : Static.StaticReturnFormed r

namespace ReturnEffect

def readsName {Γ : TypeEnv} {r : CppReturn}
    (_ : ReturnEffect Γ r) : NameSet :=
  fun x => ReturnReadsName r x

end ReturnEffect

/-- Effect surface for a jump. -/
structure JumpEffect (Γ : TypeEnv) (j : CppJump) : Type where
  formed : Static.StaticJumpFormed j

namespace JumpEffect

def readsName {Γ : TypeEnv} {j : CppJump}
    (_ : JumpEffect Γ j) : NameSet :=
  fun x => JumpReadsName j x

end JumpEffect

end Effects
end Cpp3
