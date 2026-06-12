import CppFormalization.Cpp4.Core.Function
import CppFormalization.Cpp4.Core.Syntax
import CppFormalization.Cpp4.Core.TypeEnv

/-!
# CppFormalization.Cpp4.Core.Program

Program-level vocabulary. `Core.Function` deliberately stops at callable
signatures/declarations; this file is the first Core layer that may mention
function bodies.
-/

namespace Cpp4

/-- Internal function definition: a signature plus a statement block body. -/
structure InternalFunctionDef where
  name : FunctionName
  sig : FunctionSig
  body : StmtBlock

namespace InternalFunctionDef

/-- Internal function definitions expose an internal callable declaration. -/
def toCallableDecl (d : InternalFunctionDef) : CallableDecl where
  sig := d.sig
  kind := .internal

end InternalFunctionDef

/-- Whole-program surface used by later typing and call semantics. -/
structure Program where
  functions : FunctionEnv
  internal : FunctionName → Option InternalFunctionDef

namespace Program

/-- Lookup a callable declaration through the program's function environment. -/
def lookupCallable (P : Program) (f : FunctionName) : Option CallableDecl :=
  P.functions.lookup f

/-- Lookup an internal function body. -/
def lookupInternal (P : Program) (f : FunctionName) : Option InternalFunctionDef :=
  P.internal f

/-- Internal definitions are consistent with the callable environment. -/
def InternalsDeclared (P : Program) : Prop :=
  ∀ {f d}, P.lookupInternal f = some d →
    P.lookupCallable f = some d.toCallableDecl

/-- A program containing no callable declarations and no internal definitions. -/
def empty : Program where
  functions := { lookup := fun _ => none }
  internal := fun _ => none

theorem lookupCallable_empty (f : FunctionName) :
    empty.lookupCallable f = none := by
  rfl

theorem lookupInternal_empty (f : FunctionName) :
    empty.lookupInternal f = none := by
  rfl

end Program

end Cpp4
