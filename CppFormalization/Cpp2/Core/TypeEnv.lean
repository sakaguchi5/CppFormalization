import CppFormalization.Cpp2.Core.Types

/-!
Scoped type environment.
-/

namespace Cpp

structure TypeFrame where
  decls : Ident → Option DeclInfo

structure TypeEnv where
  scopes : List TypeFrame

instance : Repr TypeEnv where
  reprPrec Γ _ :=
    "TypeEnv { scopes := " ++ repr Γ.scopes.length ++ " }"

def emptyTypeFrame : TypeFrame := {
  decls := fun _ => none
}

def emptyTypeEnv : TypeEnv := {
  scopes := [emptyTypeFrame]
}

instance : Inhabited TypeEnv where
  default := emptyTypeEnv

def lookupDeclFrames : List TypeFrame → Ident → Option DeclInfo
  | [], _ => none
  | fr :: frs, x =>
      match fr.decls x with
      | some d => some d
      | none => lookupDeclFrames frs x

def lookupDecl (Γ : TypeEnv) (x : Ident) : Option DeclInfo :=
  lookupDeclFrames Γ.scopes x

def pushTypeScope (Γ : TypeEnv) : TypeEnv :=
  { Γ with scopes := emptyTypeFrame :: Γ.scopes }

def currentTypeScopeFresh (Γ : TypeEnv) (x : Ident) : Prop :=
  match Γ.scopes with
  | [] => False
  | fr :: _ => fr.decls x = none

def withTopTypeFrame (Γ : TypeEnv) (fr : TypeFrame) : TypeEnv :=
  match Γ.scopes with
  | [] => { scopes := [fr] }
  | _ :: frs => { scopes := fr :: frs }

def insertTopDecl (Γ : TypeEnv) (x : Ident) (d : DeclInfo) : TypeEnv :=
  match Γ.scopes with
  | [] =>
      { scopes := [{ decls := fun y => if y = x then some d else none }] }
  | fr :: frs =>
      { scopes :=
          { fr with decls := fun y => if y = x then some d else fr.decls y } :: frs }

def declareTypeObject (Γ : TypeEnv) (x : Ident) (τ : CppType) : TypeEnv :=
  insertTopDecl Γ x (.object τ)

def declareTypeRef (Γ : TypeEnv) (x : Ident) (τ : CppType) : TypeEnv :=
  insertTopDecl Γ x (.ref τ)

end Cpp
