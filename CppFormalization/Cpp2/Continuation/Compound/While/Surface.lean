import CppFormalization.Cpp2.Closure.Progress.While.BodyLocal
import CppFormalization.Cpp2.Continuation.Compound.While.Tail.Lifting
import CppFormalization.Cpp2.Closure.Lifting.While.Exit.Lifting

namespace Cpp
namespace CompoundContinuation
namespace While

/-!
# While surface

While is the same-statement backedge instance of the compound-continuation
pattern.
-/

structure NormalTailSurface
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyNormalRoute cond σ1) : Type where
  continuation : Backedge.NormalContinuationInput route
  adequacy : Tail.NormalAdequacyDemand route
  proof : Tail.NormalProofDemand route

def NormalTailSurface.toPackage
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (h : NormalTailSurface route) :
    Tail.NormalPackage route :=
  { continuation := h.continuation
    adequacy := h.adequacy
    tailProof := h.proof }

structure ContinueTailSurface
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyContinueRoute cond σ1) : Type where
  continuation : Backedge.ContinueContinuationInput route
  adequacy : Tail.ContinueAdequacyDemand route
  proof : Tail.ContinueProofDemand route

def ContinueTailSurface.toPackage
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (h : ContinueTailSurface route) :
    Tail.ContinuePackage route :=
  { continuation := h.continuation
    adequacy := h.adequacy
    tailProof := h.proof }

end While
end CompoundContinuation
end Cpp
