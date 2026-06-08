/-
Allファイルはグラフ化して効率的にたどるための記録でしかなく
buildを示すものではない
-/
/-
Cpp2 は、巨大 mutual typing から上層が情報を取り出していく設計。
Cpp3 の上層は「Cpp2 master の上層をコピーしたもの」ではなく、Typing mutual の分解から自然に生える設計。
-/
import CppFormalization.Cpp3.Core.All
import CppFormalization.Cpp3.Contracts.Core.All
import CppFormalization.Cpp3.Typing.Micro.All
import CppFormalization.Cpp3.Typing.Judgment.All
import CppFormalization.Cpp3.Semantics.All
import CppFormalization.Cpp3.Static.All
import CppFormalization.Cpp3.Effects.All
import CppFormalization.Cpp3.SafetyFragment.All
import CppFormalization.Cpp3.Boundary.All
import CppFormalization.Cpp3.Stability.All
import CppFormalization.Cpp3.Continuation.All
