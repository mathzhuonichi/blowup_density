# Lane 247 — R47 grid lemmas

## 1. 证了哪个定理

在注册的 `Contracts.V1.Data.Grid` / `gridObservation` 词汇中证明了
Theorem 4.7 所需的两个引理：

- `exists_ball_in_common_cell`：任意有限个网格都有同一个正半径开球，
  且该球在每个网格中都包含于某个半开 cell。证明实际调用了更强的
  `Paper3.finite_grids_common_ball`，后者把球放进对应的开 cell interior。
- `gridObservation_locality`：若 `z₁-z₂` 的拓扑支撑包含在 `B` 中，
  `B` 包含于 cell `k₀`，两场在该 cell 上可积，且差在该 cell 上的
  向量积分为零，则两个注册的完整网格观测函数相等。

## 2. Lean 里现在有什么

实现位于 `verification/Bindings/GridLemmas.lean`。locality 证明直接处理
注册的半开 cells：在 containing cell 上用可积性拆分 Bochner 积分；
在其他 cell 上证明半开 cells 两两不交，再由拓扑支撑包含得到逐点相等。
因此不需要把 reconciled spec 的 `ball ⊆ cell` 偷换成
`ball ⊆ cellInterior`，也不要求所有其他 cells 上的额外可积性。

审计文件 `research/R47/axioms_grid_lemmas.lean` 给两个声明逐一运行
`#print axioms`，两者都恰为
`[propext, Classical.choice, Quot.sound]`，并含 common-ball 与 locality 的
非空洞例子。正负路线与 statement-fidelity 决定记录在
`research/R47/ATTEMPTS_GRID_LEMMAS.md`。

## 3. 缺口是什么

本 lane 只给出几何与观测 locality，不装配完整 `RGridFamily`。显式的
零 cell 积分是假设，不能只由支撑包含推出：

- velocity 差的该假设由光滑、紧支撑和
  `velocityDifference_divFree`，经已有
  `Paper3.setIntegral_component_eq_zero` 分量逐一推出；
- force 差不应假设 divergence-free，它的零积分须按论文
  `eq:gridforce` 从两条动量方程、velocity 的零均值及边界附近消失推出。

`Contracts/V1/Packet.lean` 没有命名的 `zero_mean` 字段；可用的是
divergence-free 与支撑性质。论文和 reconciled spec 都不要求球靠近预先
指定的点或落在预给 open set 中，因此没有增加该强化版本；请求签名中的
`x : Space` 为保持接口而保留，但结论不依赖它。

## 4. 跑了什么命令、什么结果

- `cd verification && LEAN_NUM_THREADS=6 lake build Bindings.GridLemmas`：通过
  （只有既有上游模块的 linter warnings）。
- `cd verification && LEAN_NUM_THREADS=6 lake env lean Bindings/GridLemmas.lean`：
  通过，0 输出。
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R47/axioms_grid_lemmas.lean`：
  通过；两个声明均只打印规定的三个公理，无 warning。
- `. scripts/lean-env.sh && make check`：通过。
- `LEAN_NUM_THREADS=6 scripts/gates.sh Bindings.GridLemmas`：通过；其中
  `make test`、`make test-mutations` 与相对
  `origin/erenup/integration` 的 contract compatibility 检查均通过。
