import CppFormalization.Cpp2.Contracts.Assumption
import CppFormalization.Cpp2.Contracts.Policy
import CppFormalization.Cpp2.Contracts.Kind
import CppFormalization.Cpp2.Contracts.Certified.All
import CppFormalization.Cpp2.Contracts.Obligations.All

/-!
# CppFormalization.Cpp2.Contracts

Contract layer between `Effects` and `Proof`.

`Certified` contains theorem-backed facts derived from effect certificates.
`Obligations` contains program-facing contract family names.
-/
