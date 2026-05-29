namespace Cpp
namespace Contracts

/-!
# CppFormalization.Cpp2.Contracts.Assumption

Contract assumptions are not axioms.

A contract is a piece of evidence passed to a theorem/definition as an argument.
This file only gives lightweight names for that discipline.
-/

universe u

/--
`Requires P` means that `P` is required as an explicit contract argument.

This is definitionally just `P`; it introduces no assumption.
-/
abbrev Requires (P : Sort u) : Sort u :=
  P

/--
`Certified P` means that `P` is expected to be theorem-backed or derived from
lower evidence such as an effect certificate.

This is definitionally just `P`; it introduces no assumption.
-/
abbrev Certified (P : Sort u) : Sort u :=
  P

/--
A provider is an explicit evidence package for a contract.

This is useful when a caller wants to pass a named object rather than a bare
proof/value.
-/
structure Provider (P : Sort u) : Sort (max 1 u) where
  evidence : P

namespace Provider

def get {P : Sort u} (p : Provider P) : P :=
  p.evidence

end Provider

end Contracts
end Cpp
