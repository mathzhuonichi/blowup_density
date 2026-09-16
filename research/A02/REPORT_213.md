# Lane 213 report

## 1. 证了哪个定理

A02 已完成无条件 `exists_maximal'`：直接把 A01 的 `localHorizon'` 和
`localCarrier.w` 代入 `exists_maximal_of_localSolution`，不再要求局部存在性输入。
同时证明寿命正性、局部视界下界和重启切片属于 `initialClassR`。
A04 已证明完整外力平移资格、每个预奇异时刻的局部重启解，以及固定平移外力
下 H⁷ 球上的统一局部解。**未完成任务要求的无条件 A04 延拓链。**

## 2. Lean 里现在有什么

新增 `Section4/A02/MaximalWiring.lean`（6 个定理）和
`Section4/A04/RestartWiring.lean`（5 个定理）；`maximal_unique` 保持不变。
两个对应 axioms 文件逐项检查新声明，另检查既有 `maximal_unique`，均恰好输出
`[propext, Classical.choice, Quot.sound]`；非空洞例子使用 `A04.zeroSol`，
并检查零初值的实际最大解存在性。两个 ATTEMPTS 文件记录证明路径与接口差异。
只新增七个文件；未修改既有模块或合同，未 push、merge 或 rebase。

## 3. 缺口是什么

`Restart` 实际是一个 Prop 定义，要求 δ 只依赖 ν 和 H¹ 界，并在所有初值、
外力、重启时刻之前选定；它没有 H² 积分假设。A01 给出的 δ 只在固定外力、
H⁷ 球上统一，对 `timeShift t₀ f` 应用后仍依赖 t₀。故不能按任务描述直接
把这条定理接成 `Restart` 或原形 `restartBeyond`。

lane 179 的 `GronwallEndpoint` 还要求同一经典解的光滑 Sobolev 路径、
闭区间柱面载体及其范数界；不是任意 `SolvesBelow` 加有限 H² 积分即可调用的
`HigherOrderBound`。既有 `A02.patch` 也只比较两个同初值、零时刻开始的解，
不是平移后的拼接定理。精确的现有开放输入仍是 `A04.Restart` 和
`A04.HigherOrderBound`；这不是仅剩一个初值资格或外力平移引理的情形。
因此没有用一个打包假设掩盖多个缺口，也没有新增声称无条件的
`restartBeyond'` / `extendsBeyond'` / `lifespanInfiniteOfLocallyFinite'`。
完整接口表见 `../A04/ATTEMPTS_RESTART_WIRING.md`。

## 4. 跑了什么命令、什么结果

每次 Lean 命令均先 `. scripts/lean-env.sh`，从 `verification/` 执行，
`LEAN_NUM_THREADS=6`。

- `lake -q --log-level=error build NSFormalization.Section4.A02.MaximalWiring NSFormalization.Section4.A04.RestartWiring`：通过，零输出。
- `lake env lean ../formalization/NSFormalization/Section4/A02/MaximalWiring.lean`：通过，零输出。
- `lake env lean ../formalization/NSFormalization/Section4/A04/RestartWiring.lean`：通过，零输出。
- `lake env lean ../research/A02/axioms_wiring.lean` 及 `../research/A04/axioms_restart_wiring.lean`：通过，12 项公理输出全部恰为标准三项，例子通过。
- 根目录 `make check`：通过，合同政策和 30 项工作队列检查通过。
- `verification/` 中 `lake test`：通过（Makefile `test` 目标的等价调用，确保 lake 从 verification 运行）。
- `python3 experiments/test_contract_mutations.py --skip-build`：通过；正常重构接受，三种违规变异均按预期拒绝。
- `git diff --check`：通过。

首次普通构建重放既有依赖的警告；新增两个文件的直接 Lean 检查均无警告。
