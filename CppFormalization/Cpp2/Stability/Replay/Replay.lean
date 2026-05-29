import CppFormalization.Cpp2.Metatheory.Contracts.Kind

namespace Cpp
namespace Contracts
namespace Obligations

def replayStable : ContractKind :=
  .obligation .replayStable

def conditionReplay : ContractKind :=
  .obligation .conditionReplay

def bodyReplay : ContractKind :=
  .obligation .bodyReplay

end Obligations
end Contracts
end Cpp
