import CppFormalization.Cpp2.Demand.Preservation.FromReady
import CppFormalization.Cpp2.Entry.StaticSafety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Preservation.Assign.Preservation
import CppFormalization.Cpp2.Preservation.DeclareObject.Preservation
import CppFormalization.Cpp2.Preservation.DeclareRef.Preservation

namespace Cpp

/-!
# Proof.Preservation.Demand.PrimitivePreservation

Primitive preservation from path-sensitive execution demand.

This is the first theorem-backed replacement point for the old
` 削除済み` route.  Primitive statements do not need tail
readiness transport.  Their demand evidence contains exactly the local
expression/place readiness consumed by the corresponding semantic step.
-/

/-- Preservation for an expression statement demand. -/
theorem exprStmt_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {e : ValExpr} :
    StmtExecutionDemand Γ σ (.exprStmt e) .normal σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand with
  | exprStmt hty hready hval =>
      simpa using hσ

/-- Preservation for an assignment demand. -/
theorem assign_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {e : ValExpr} :
    StmtExecutionDemand Γ σ (.assign p e) .normal σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand with
  | assign hpty hpready hvty heready hval hassign =>
      have hvcompat : ValueCompat _ _ :=
        expr_ready_eval_compat heready hval
      exact assigns_preserves_scoped_typed_state_concrete
        hσ hpty hpready hvcompat hassign

/-- Preservation for object declaration without initializer demand. -/
theorem declareObjNone_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} :
    StmtExecutionDemand Γ σ (.declareObj τ x none) .normal σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand with
  | declareObjNone hfresh hobj hdecl =>
      exact declares_object_preserves_scoped_typed_state_concrete
        hfresh hσ hdecl

/-- Preservation for object declaration with initializer demand. -/
theorem declareObjSome_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {e : ValExpr} :
    StmtExecutionDemand Γ σ (.declareObj τ x (some e)) .normal σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand with
  | declareObjSome hfresh hobj hty heready hval hdecl =>
      exact declares_object_preserves_scoped_typed_state_concrete
        hfresh hσ hdecl

/-- Preservation for reference declaration demand. -/
theorem declareRef_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p : PlaceExpr} :
    StmtExecutionDemand Γ σ (.declareRef τ x p) .normal σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand with
  | declareRef hfresh hpty hpready hplace hdecl =>
      exact declares_ref_preserves_scoped_typed_state_concrete
        hfresh hσ hdecl

/--
Aggregate preservation theorem for primitive normal statement demands.

This intentionally covers only the constructors whose execution does not recurse
into a tail statement or block.  Composite constructs are handled by the future
demand recursor using their embedded sub-demands.
-/
theorem primitive_stmt_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    (match st with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) →
    StmtExecutionDemand Γ σ st .normal σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hdemand hσ
  cases st <;> simp at hprim
  case skip =>
    cases hdemand
    simpa using hσ
  case exprStmt e =>
    exact exprStmt_preserves_from_demand hdemand hσ
  case assign p e =>
    exact assign_preserves_from_demand hdemand hσ
  case declareObj τ x oe =>
    cases oe with
    | none =>
        exact declareObjNone_preserves_from_demand hdemand hσ
    | some e =>
        exact declareObjSome_preserves_from_demand hdemand hσ
  case declareRef τ x p =>
    exact declareRef_preserves_from_demand hdemand hσ

/-- Abrupt primitive statements preserve the state unchanged. -/
theorem break_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} :
    StmtExecutionDemand Γ σ .breakStmt .breakResult σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand
  simpa using hσ

/-- Abrupt primitive statements preserve the state unchanged. -/
theorem continue_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} :
    StmtExecutionDemand Γ σ .continueStmt .continueResult σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand
  simpa using hσ

/-- Return without value preserves the state unchanged. -/
theorem returnNone_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} :
    StmtExecutionDemand Γ σ (.returnStmt none) (.returnResult none) σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand
  simpa using hσ

/-- Return with value preserves the state unchanged. -/
theorem returnSome_preserves_from_demand
    {Γ Δ : TypeEnv} {σ σ' : State} {e : ValExpr} {v : Value} :
    StmtExecutionDemand Γ σ (.returnStmt (some e)) (.returnResult (some v)) σ' Δ →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hdemand hσ
  cases hdemand
  simpa using hσ

end Cpp
