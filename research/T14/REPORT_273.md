# 273-SPEC-t14-draft-a report

## 1. 拟定了哪个定理

完成 T14 双盲草案 A：对每个 `ν > 0`，导入已经注册的欧氏紧支爆破解
`PacketAPI ν`，保留显式数据 `(U,P,F,K,M,D,τ)`，并补上论文
`eq:packetenergy` 的完整链式关系。量词顺序逐字保持为
`∀ ν, 0 < ν → ∃ packet`；本 lane 只写陈述，没有证明。

## 2. Lean 里现在有什么

- `DraftA.lean` 定义了局部量 `packetForceAccumulation`、单黏性接口
  `TorusPacketEnergyAPI`、命题形式 `torusPacketEnergyStatement` 和选定族
  `TorusPacketEnergyFamily`。
- 新接口结构性继承 `Contracts.V1.PacketAPI`，所以 `thm:packet`、精确
  `M/D`、共同初始静止区间、速度/压力负时间光滑零延拓以及延拓后的
  方程和无散性全部逐字复用。
- 唯一新增的证明义务是 `packet_energy`：同时保存
  `A ≤ B` 和 `B = N(t)^2`，没有用较弱的 `A ≤ N(t)^2` 替代。
- `COMPARISON_A.md` 给出论文条款到 Lean 字段的逐项表、设计选择、歧义、
  待证引理和 Section 4 对应物。

## 3. 缺口是什么

- 现有 `Bindings.packet ν hν` 尚未携带 `eq:packetenergy`；定稿注册时要从
  紧支能量恒等式、正则化平方根估计和单调收敛证明该字段。
- 还需证明 `2∫ ‖F‖₂N = N²` 的绝对连续性/微积分引理，以及点态 `IsLUB`
  与后续 `L∞_tL²_x` 本质上确界的桥。
- T14 的包仍是欧氏源包。缩放后放入单坐标球、单拷贝周期化及其
  `L²`/耗散换元恒等式属于 T15；这里没有假设任意未缩放紧支集能装进
  单位基本立方体。
- 本节点不使用 T10 的周期 Sobolev 定义；`lp (Fin 3 → ℤ) 2` 与
  `(1+4π²|k|²)^(s/2)` 在 T13/T15 才进入。

## 4. 跑了什么命令、什么结果

- 用 `#check` 核对了 `Set.Ioc`、`Set.Ico`、`IntegrableOn`、`Real.sqrt`、
  `IsLUB`、`PacketAPI`、`PacketFamily`、`l2Sq`、`dissipation` 和
  `zeroPastField`；全部由当前 Lean/Mathlib 环境解析。
- `cd verification && lake env lean ../research/T14/DraftA.lean`：通过，退出码
  `0`，无错误。
- `make check`：通过，退出码 `0`；输出仍列出仓库既有的
  `Paper1/BoundaryCorollary.lean:90` 占位和 source-hash 诊断，本 lane 未触碰
  这些文件。
- `make test`：通过，退出码 `0`；只有既有依赖的 linter warning。
- `make test-mutations`：通过；四类 mutation 结果为预期，suite 报告
  `Mutation suite passed`。
