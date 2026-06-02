import CppFormalization.Cpp2.Entry.Body.BodyReadyCI
import CppFormalization.Cpp2.Entry.Facts.Control.BodyReadyControlExclusionCI
import CppFormalization.Cpp2.Closure.Package.BodyClosureBoundaryCI

namespace Cpp

private theorem frame_eq_of_scope_lookup
    {σ : State} {k : Nat} {fr₁ fr₂ : ScopeFrame}
    (h₁ : σ.scopes[k]? = some fr₁)
    (h₂ : σ.scopes[k]? = some fr₂) :
    fr₁ = fr₂ := by
  apply Option.some.inj
  exact h₁.symm.trans h₂

namespace BodyReadyCI

def toStructural
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyStructuralBoundary Γ st :=
  h.structural

def toStatic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyStaticBoundaryCI Γ st :=
  h.static

def toTyped0
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    WellTypedFrom Γ st :=
  h.static.typed0

def toProfile
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyControlProfile Γ st :=
  h.static.profile

def toEntry
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyEntryWitness Γ st :=
  h.static.root

def toDynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyDynamicBoundary Γ σ st :=
  h.dynamic

def toAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyAdequacyCI Γ σ st h.static.profile :=
  h.adequacy



end BodyReadyCI

namespace BlockBodyReadyCI

def toStructural
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyStructuralBoundary Γ ss :=
  h.structural

def toStatic
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyStaticBoundaryCI Γ ss :=
  h.static

def toProfile
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyControlProfile Γ ss :=
  h.static.profile

def toEntry
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyEntryWitness Γ ss :=
  h.static.root

def toDynamic
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyDynamicBoundary Γ σ ss :=
  h.dynamic

def toAdequacy
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyAdequacyCI Γ σ ss h.static.profile :=
  h.adequacy

def toClosureBoundary
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyClosureBoundaryCI Γ σ ss :=
  mkBlockBodyClosureBoundaryCI h.structural h.static h.dynamic h.adequacy

end BlockBodyReadyCI

def legacyStmtReady_of_static_dynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStaticBoundaryCI Γ st)
    (hd : BodyDynamicBoundary Γ σ st) :
    StmtReady Γ σ st :=
  ⟨hs.typed0, noUninit_of_stmtReadyConcrete hd.safe, noInvalidRef_of_stmtReadyConcrete hd.safe⟩

end Cpp
