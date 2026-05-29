-- removed ideal relayout: import CppFormalization.Cpp2.All  -- All.lean excluded

/-!
# CppFormalization.Cpp2.MainlineAxiomAudit

目的:
- `All.lean` を本線判定の根拠にはしない。
- ただし、調査時には全宣言をロードする入口として使う。
- 本線 root / mainline candidate / compatibility residue / contract debt に
  `#check` と `#print axioms` をかけ、実際にどの axiom を踏んでいるかを見る。
- 必要なthoremを適宜追加して、調査を終えたら削除する
実行例:
```bash
lake env lean CppFormalization/Cpp2/MainlineAxiomAudit.lean
```

読み方:
- `#print axioms <name>` に出る axiom が、その `<name>` の実依存。
- `All.lean` に import されているだけでは「本線で生きている」とは判定しない。
- 本線判定は、このファイルで root として採用した theorem からの依存だけで行う。
- `propext`, `Classical.choice`, `Quot.sound` など Lean/Mathlib 側の基礎 axiom が
  出ることがある。まず見るべきは Cpp 名前空間内の axiom。
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option pp.all false

namespace Cpp


end Cpp
