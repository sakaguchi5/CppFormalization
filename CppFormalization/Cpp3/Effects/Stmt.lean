import CppFormalization.Cpp3.Effects.Primitive
import CppFormalization.Cpp3.Static.BoundaryInfo

/-!
# CppFormalization.Cpp3.Effects.Stmt

Statement and block effect surfaces.

This is still an effect-description layer.  It summarizes what a statement or
block may read, directly write, or bind, but it does not say that those accesses
are safe and it does not prove that later boundaries survive them.
-/

namespace Cpp3
namespace Effects

/-- Effect surface for a statement. -/
structure StmtEffect (Γ : TypeEnv) (st : CppStmt) : Type where
  formed : Static.StaticStmtFormed st

namespace StmtEffect

def readsName {Γ : TypeEnv} {st : CppStmt}
    (_ : StmtEffect Γ st) : NameSet :=
  fun x => StmtReadsName st x

def writesDirectName {Γ : TypeEnv} {st : CppStmt}
    (_ : StmtEffect Γ st) : NameSet :=
  fun x => StmtWritesDirectName st x

def bindsName {Γ : TypeEnv} {st : CppStmt}
    (_ : StmtEffect Γ st) : NameSet :=
  fun x => StmtBindsName st x

/-- A statement effect obtained from static statement boundary information. -/
def ofStaticBoundary
    {Γ : TypeEnv} {st : CppStmt}
    (h : Static.StaticStmtBoundaryInfo Γ st) : StmtEffect Γ st where
  formed := h.entry.formed

end StmtEffect

/-- Effect surface for a block body. -/
structure BlockEffect (Γ : TypeEnv) (ss : StmtBlock) : Type where
  formed : Static.StaticBlockFormed ss

namespace BlockEffect

def readsName {Γ : TypeEnv} {ss : StmtBlock}
    (_ : BlockEffect Γ ss) : NameSet :=
  fun x => BlockReadsName ss x

def writesDirectName {Γ : TypeEnv} {ss : StmtBlock}
    (_ : BlockEffect Γ ss) : NameSet :=
  fun x => BlockWritesDirectName ss x

def bindsName {Γ : TypeEnv} {ss : StmtBlock}
    (_ : BlockEffect Γ ss) : NameSet :=
  fun x => BlockBindsName ss x

/-- A block effect obtained from static block boundary information. -/
def ofStaticBoundary
    {Γ : TypeEnv} {ss : StmtBlock}
    (h : Static.StaticBlockBoundaryInfo Γ ss) : BlockEffect Γ ss where
  formed := h.entry.formed

end BlockEffect

/-- Effect surface for a function body. -/
structure FunctionBodyEffect (Γ : TypeEnv) (body : CppStmt) : Type where
  static : Static.StaticFunctionBodyBoundaryInfo Γ body
  effect : StmtEffect Γ body

namespace FunctionBodyEffect

def readsName {Γ : TypeEnv} {body : CppStmt}
    (h : FunctionBodyEffect Γ body) : NameSet :=
  h.effect.readsName

def writesDirectName {Γ : TypeEnv} {body : CppStmt}
    (h : FunctionBodyEffect Γ body) : NameSet :=
  h.effect.writesDirectName

def bindsName {Γ : TypeEnv} {body : CppStmt}
    (h : FunctionBodyEffect Γ body) : NameSet :=
  h.effect.bindsName

end FunctionBodyEffect

end Effects
end Cpp3
