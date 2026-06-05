import CppFormalization.Cpp3.Typing.Judgment.Reconstruction

namespace Cpp3
namespace Typing
namespace Judgment

/-!
# CppFormalization.Cpp3.Typing.Judgment.Surface

Surface names for the Cpp3 control-indexed judgment.

The old Cpp2 names are not imported.  These aliases are provided only so that
future Cpp3 layers can state the familiar shape while the implementation remains
the microkernel reconstruction in `StmtTyping` / `BlockTyping`.
-/

/-- Surface alias for Cpp3 statement control-indexed typing. -/
abbrev HasTypeStmtCI : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop :=
  StmtTyping

/-- Surface alias for Cpp3 block-body control-indexed typing. -/
abbrev HasTypeBlockCI : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop :=
  BlockTyping

end Judgment
end Typing
end Cpp3
