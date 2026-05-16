import CppFormalization.Cpp2.Proof.Preservation.StmtBlockNormalWitness
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernel
import CppFormalization.Cpp2.Proof.Preservation.WhileDecompositionFacts
import CppFormalization.Cpp2.Proof.Preservation.WhileReentryReady
import CppFormalization.Cpp2.Proof.Preservation.BlockNormalPreservation
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernelSupport
import CppFormalization.Cpp2.Proof.Preservation.StmtControlPreservation
import CppFormalization.Cpp2.Proof.Preservation.StmtControlRecursorCore
import CppFormalization.Cpp2.Proof.Preservation.StmtNormalWitness
import CppFormalization.Cpp2.Proof.Preservation.StmtWhileNormalWitness
import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandRecursorCore
import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandResidualBoundary
import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandSequentialResidual
import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandBlockResidual

import CppFormalization.Cpp2.Proof.Preservation.Scope.All
import CppFormalization.Cpp2.Proof.Preservation.Assign.All
import CppFormalization.Cpp2.Proof.Preservation.DeclareRef.All
import CppFormalization.Cpp2.Proof.Preservation.DeclareObject.All

/-!
# CppFormalization.Cpp2.Proof.Preservation.All

Exhaustive aggregate for this directory.

This file imports every Lean file directly under this directory, except itself,
and every immediate child directory through that child directory's `All.lean`.
-/
