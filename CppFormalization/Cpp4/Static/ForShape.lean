import CppFormalization.Cpp4.Static.SyntaxShape

/-!
# CppFormalization.Cpp4.Static.ForShape

Static surface facts specific to C++ `for` syntax.
-/

namespace Cpp4

namespace StaticFor

/-- Shape of an optional `for` condition. -/
def OptionalCondShape : Option CppCond → Prop
  | none => True
  | some c => StaticCondShape c

/-- The initializer fragment is one of the surface forms accepted by Cpp4. -/
def InitShape (init : CppForInit) : Prop :=
  StaticForInitShape init

/-- The iteration fragment is one of the surface forms accepted by Cpp4. -/
def IterShape (iter : CppForIter) : Prop :=
  StaticForIterShape iter

/-- Complete static shape of a surface `for` loop. -/
structure LoopShape (init : CppForInit) (cond : Option CppCond)
    (iter : CppForIter) (body : CppStmt) : Type where
  initShape : InitShape init
  condShape : OptionalCondShape cond
  iterShape : IterShape iter
  bodyShape : StaticStmtShape body

namespace LoopShape

/-- Repackage a complete `for` shape as the generic surface-loop shape. -/
def toStaticLoopShape {init : CppForInit} {cond : Option CppCond}
    {iter : CppForIter} {body : CppStmt}
    (h : LoopShape init cond iter body) :
    StaticLoopShape (.forLoop init cond iter body) :=
  StaticLoopShape.forLoop h.initShape h.condShape h.iterShape h.bodyShape

end LoopShape

end StaticFor

end Cpp4
