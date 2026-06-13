import CppFormalization.Cpp4.Core.Function

/-!
# CppFormalization.Cpp4.Static.Ident

Static identifier facts for the Cpp4 surface layer.

Core syntax deliberately stores raw `Ident` values.  This file is the first
Static layer that says which raw spellings are acceptable as user-defined names
and when a list of names is duplicate-free.
-/

namespace Cpp4

/-- A raw ordinary identifier is statically usable by a user declaration. -/
def StaticUserIdent (x : Ident) : Prop :=
  ValidUserIdent x

/-- A function name is statically usable when its raw spelling is not reserved. -/
def StaticFunctionName (f : FunctionName) : Prop :=
  f.valid

/-- All raw names in a list are valid user identifiers. -/
def StaticUserIdentList (xs : List Ident) : Prop :=
  ∀ x, x ∈ xs → StaticUserIdent x

/-- No duplicate ordinary names. -/
def StaticNamesNoDup (xs : List Ident) : Prop :=
  xs.Nodup

namespace Param

/-- The ordinary name introduced by a parameter. -/
def staticName (p : Param) : Ident :=
  p.name

/-- A parameter has a statically valid name. -/
def StaticName (p : Param) : Prop :=
  StaticUserIdent p.name

end Param

namespace FunctionSig

/-- Parameter names in source order. -/
def paramNames (sig : FunctionSig) : List Ident :=
  sig.params.map Param.staticName

/-- No duplicate parameter names. -/
def ParamsNoDup (sig : FunctionSig) : Prop :=
  sig.paramNames.Nodup

/-- Every parameter name is statically valid. -/
def ParamsValidNames (sig : FunctionSig) : Prop :=
  ∀ p, p ∈ sig.params → p.StaticName

end FunctionSig

end Cpp4
