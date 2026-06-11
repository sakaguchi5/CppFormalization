import CppFormalization.Cpp4.Core.Type

/-!
# CppFormalization.Cpp4.Core.TypeEnv

Static type environments for Cpp4.  This layer records only name-to-declaration
information; control permissions and callable lookup stay in `ControlContext` and
`FunctionEnv`.
-/

namespace Cpp4

/-- Static environment for ordinary object/reference names. -/
structure TypeEnv where
  lookup : Ident → Option DeclInfo

namespace TypeEnv

/-- Empty static environment. -/
def empty : TypeEnv where
  lookup := fun _ => none

/-- A name is statically fresh in an environment. -/
def Fresh (Γ : TypeEnv) (x : Ident) : Prop :=
  Γ.lookup x = none

/-- A name is bound to a declaration entry in an environment. -/
def Bound (Γ : TypeEnv) (x : Ident) (info : DeclInfo) : Prop :=
  Γ.lookup x = some info

/-- Bind or shadow a name.  Scope discipline later decides when shadowing is allowed. -/
def bind (Γ : TypeEnv) (x : Ident) (info : DeclInfo) : TypeEnv where
  lookup := fun y => if y = x then some info else Γ.lookup y

/-- Extend an environment by a list of declarations, left-to-right. -/
def bindMany : TypeEnv → List (Ident × DeclInfo) → TypeEnv
  | Γ, [] => Γ
  | Γ, (x, info) :: xs => bindMany (bind Γ x info) xs

theorem lookup_empty (x : Ident) :
    empty.lookup x = none := by
  rfl

theorem lookup_bind_same (Γ : TypeEnv) (x : Ident) (info : DeclInfo) :
    (bind Γ x info).lookup x = some info := by
  simp [bind]

theorem lookup_bind_other {Γ : TypeEnv} {x y : Ident} {info : DeclInfo}
    (h : y ≠ x) :
    (bind Γ x info).lookup y = Γ.lookup y := by
  simp [bind, h]

theorem fresh_iff_lookup_none {Γ : TypeEnv} {x : Ident} :
    Fresh Γ x ↔ Γ.lookup x = none := by
  rfl

theorem bound_iff_lookup_some {Γ : TypeEnv} {x : Ident} {info : DeclInfo} :
    Bound Γ x info ↔ Γ.lookup x = some info := by
  rfl

end TypeEnv

end Cpp4
