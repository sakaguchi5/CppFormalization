import CppFormalization.Cpp2.Operational.Stmt
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete
import CppFormalization.Cpp2.Static.Typing.ControlIndexed

namespace Cpp

/-!
# CppFormalization.Cpp2.Effects.NormalHeadContext

Axiom-free effect-layer context for one normal head step.

This file intentionally sits above `Static` and below `Closure`.
It imports syntax, typing, statement semantics, concrete readiness and concrete
state invariants, but it imports no `Closure.*` module.
-/

/--
A normal head-step context.

`Γ, σ` are the pre typing/runtime worlds.
`Δ, σ'` are the post typing/runtime worlds produced by the normal head.
`head` is the single statement whose normal execution creates the effect.
-/
structure NormalHeadCtx
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop where
  typing : HasTypeStmtCI .normalK Γ head Δ
  step : BigStepStmt σ head .normal σ'
  post : ScopedTypedStateConcrete Δ σ'

/--
A ready normal head-step context.  This is the entry object from which later
readiness-transport theorems should consume effects.
-/
structure ReadyNormalHeadCtx
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop extends
    NormalHeadCtx Γ Δ σ σ' head where
  pre : ScopedTypedStateConcrete Γ σ
  ready : StmtReadyConcrete Γ σ head

/-- Primitive statements that can serve as one normal head in the effect layer. -/
inductive PrimitiveNormalHead : CppStmt → Prop where
  | skip : PrimitiveNormalHead .skip
  | exprStmt {e : ValExpr} : PrimitiveNormalHead (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} : PrimitiveNormalHead (.assign p e)
  | declareObjNone {τ : CppType} {x : Ident} :
      PrimitiveNormalHead (.declareObj τ x none)
  | declareObjSome {τ : CppType} {x : Ident} {e : ValExpr} :
      PrimitiveNormalHead (.declareObj τ x (some e))
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} :
      PrimitiveNormalHead (.declareRef τ x p)

/-- Normal heads that preserve the type environment in the effect layer. -/
inductive EffectEnvPreservingNormalHead : CppStmt → Prop where
  | skip : EffectEnvPreservingNormalHead .skip
  | exprStmt {e : ValExpr} : EffectEnvPreservingNormalHead (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} : EffectEnvPreservingNormalHead (.assign p e)

/-- Normal heads that extend the type environment by a fresh declaration in the effect layer. -/
inductive EffectEnvExtendingNormalHead : CppStmt → Prop where
  | declareObjNone {τ : CppType} {x : Ident} :
      EffectEnvExtendingNormalHead (.declareObj τ x none)
  | declareObjSome {τ : CppType} {x : Ident} {e : ValExpr} :
      EffectEnvExtendingNormalHead (.declareObj τ x (some e))
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} :
      EffectEnvExtendingNormalHead (.declareRef τ x p)

end Cpp
