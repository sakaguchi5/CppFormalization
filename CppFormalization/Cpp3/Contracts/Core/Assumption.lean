namespace Cpp3
namespace Contracts

/-!
# CppFormalization.Cpp3.Contracts.Core.Assumption

Contracts are explicit evidence, not axioms.

`Requires P` and `Certified P` are definitionally just `P`; they only make the
role of an argument visible in theorem statements and component packages.
-/

universe u

/-- `Requires P` means that `P` is supplied as an explicit program-facing
contract argument.  This introduces no global assumption. -/
abbrev Requires (P : Sort u) : Sort u :=
  P

/-- `Certified P` means that `P` is expected to be derived from lower evidence,
such as a typing component, effect certificate, or preservation theorem. -/
abbrev Certified (P : Sort u) : Sort u :=
  P

/-- A named explicit evidence package for a contract or certificate. -/
structure Provider (P : Sort u) : Sort (max 1 u) where
  evidence : P

namespace Provider

/-- Project the evidence carried by a provider. -/
def get {P : Sort u} (p : Provider P) : P :=
  p.evidence

end Provider

end Contracts
end Cpp3
