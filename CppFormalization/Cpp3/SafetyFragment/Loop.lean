import CppFormalization.Cpp3.SafetyFragment.Footprint
import CppFormalization.Cpp3.SafetyFragment.Deref

/-!
# CppFormalization.Cpp3.SafetyFragment.Loop

Loop-specific safety obligations.

These obligations are about safe re-entry, not termination.  A safe C++ loop may
still diverge; Soundness should classify that as divergence rather than stuck.
-/

namespace Cpp3
namespace SafetyFragment

/-- The loop body preserves the next guard evaluation. -/
structure LoopGuardPreservedByBody
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Type where
  surface : Effects.WhileEffectSurface Γ Γc cond body
  kind : Contracts.ContractKind :=
    .obligation .loopGuardPreservedByBody
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace LoopGuardPreservedByBody

def get
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : LoopGuardPreservedByBody Γ Γc cond body) : h.obligation :=
  h.evidence

end LoopGuardPreservedByBody

/-- The loop body preserves the boundary needed at the backedge. -/
structure LoopBodyPreservesBackedgeBoundary
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Type where
  surface : Effects.WhileEffectSurface Γ Γc cond body
  kind : Contracts.ContractKind :=
    .obligation .loopBodyPreservesBackedgeBoundary
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace LoopBodyPreservesBackedgeBoundary

def get
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : LoopBodyPreservesBackedgeBoundary Γ Γc cond body) : h.obligation :=
  h.evidence

end LoopBodyPreservesBackedgeBoundary

/-- The loop condition can be replayed safely after re-entering the loop. -/
structure ConditionReplayStable
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Type where
  surface : Effects.WhileEffectSurface Γ Γc cond body
  kind : Contracts.ContractKind :=
    .obligation .conditionReplayStable
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace ConditionReplayStable

def get
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : ConditionReplayStable Γ Γc cond body) : h.obligation :=
  h.evidence

end ConditionReplayStable

/-- Compact loop-safety package. -/
structure LoopSafetyFragment
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Type where
  guardPreserved : LoopGuardPreservedByBody Γ Γc cond body
  backedgePreserved : LoopBodyPreservesBackedgeBoundary Γ Γc cond body
  conditionReplay : ConditionReplayStable Γ Γc cond body

end SafetyFragment
end Cpp3
