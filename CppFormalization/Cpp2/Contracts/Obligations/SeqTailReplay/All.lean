import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Basic
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.RuntimeComponents
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.BaseMaterialization
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.PureExpr
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Place
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Load
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Deref
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.ValueExpr
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Stmt
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Structured
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Full
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Stability

/-!
# SeqTailReplay aggregate

Route-local seq-tail replay/stability obligations split into focused modules.
-/
