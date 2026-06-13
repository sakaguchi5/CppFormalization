import CppFormalization.Cpp4.Static.SyntaxShape
import CppFormalization.Cpp4.Core.Program

/-!
# CppFormalization.Cpp4.Static.FunctionShape

Typing-independent static shape for function signatures and internal function bodies.
-/

namespace Cpp4

/-- Static shape of one function parameter. -/
structure ParamStaticShape (p : Param) : Type where
  nameValid : p.StaticName
  typeShape : StaticTypeShape p.ty

/-- Static shape of a function signature. -/
structure FunctionSigStaticShape (sig : FunctionSig) : Type where
  paramsShape : ∀ p, p ∈ sig.params → ParamStaticShape p
  paramsNoDup : sig.ParamsNoDup
  returnShape : StaticTypeShape sig.ret

/-- Static shape of a surface function body. -/
structure FunctionBodyStaticShape (sig : FunctionSig) (body : StmtBlock) : Type where
  sigShape : FunctionSigStaticShape sig
  bodyShape : StaticBlockShape body

/-- Static shape of an internal function definition. -/
structure InternalFunctionStaticShape (d : InternalFunctionDef) : Type where
  nameValid : StaticFunctionName d.name
  bodyShape : FunctionBodyStaticShape d.sig d.body

namespace InternalFunctionStaticShape

/-- Extract body shape from an internal function shape certificate. -/
def blockShape {d : InternalFunctionDef} (h : InternalFunctionStaticShape d) :
    StaticBlockShape d.body :=
  h.bodyShape.bodyShape

end InternalFunctionStaticShape

end Cpp4
