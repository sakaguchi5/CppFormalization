import CppFormalization.Cpp2.Contracts.Kind

namespace Cpp
namespace Contracts
namespace Obligations

def loopReentry : ContractKind :=
  .obligation .loopReentry

def whileBackedge : ContractKind :=
  .obligation .whileBackedge

end Obligations
end Contracts
end Cpp
