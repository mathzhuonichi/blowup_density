# Lane 215 report

## 1. 证了哪个定理

无条件证明 `restartFixedForce_of_memForceR`：对固定 ν>0、`MemForceR f`、
S≥0 和有限 H⁷ 界 K，先选一个 δ>0，再对所有 `t₀∈[0,S]` 及所有合格、
H⁷ 范数≤K 的初值证明 `δ ≤ localHorizon' ν a' (timeShift t₀ f)`。
使用 `[0,S+1]` 上的 H⁶ 连续外力路径范数及 lane 211 的反单调视界，
没有使用无法比较到指定视界的 vendor 存在性选择。

同时无条件证明 `higherOrderBound_of_gronwall : HigherOrderBound`，定义完全
不改：有限 `squaredHTwoIntegral S u` 推出每个自然数阶在整个 `[0,S)` 上
有有限 ENNReal 一致界。**无条件的完整延拓链尚未完成；剩一个具名拼接输入。**

## 2. Lean 里现在有什么

新增 `Section4/A04/RestartFixedForce.lean`，共 16 个声明。其中
`shiftedSolution` 构造平移后的经典解；`exists_carrier_window` 在每个时刻
之前选重启点，使局部构造器的视界覆盖该时刻；唯一性与 Sobolev 数据唯一性
给出任意经典解的 `classical_hasSmoothSobolevPath`。这个证明仅使用严格
内区间的紧致 H⁷ 界，不使用待证延拓结论。

`localCarrier_gronwall_bound` 把同一 `LocalCarrier.w` 的全部闭柱面输入
直接送入 lane 179，取 R 为其路径范数。对任意 `SolvesBelow` 家族则直接
使用 lane 179 的底层 `highOrder_bddAbove_of_kbnd`：真实 H² 积分给出统一
实数 cap，较短区间的选取不改变 Grönwall 常数，最后从 max(m,3) 降阶。
没有假设解在可能奇异的 S 处已有闭区间载体。

三个消费者 `restartBeyond_fixed`、`extendsBeyond_fixed`、
`lifespanInfiniteOfLocallyFinite_fixed` 已证明；另两个 `…_of_memForceR`
推论已消去统一重启窗口与高阶界输入。新增 ATTEMPTS、公理审计与本报告，
按任务要求更新 COMPARISON；所有既有 Lean 模块、合同和 A04 定义保持不动。

## 3. 缺口是什么

唯一保留的输入是 `extension : ShiftedLocalExtension`，精确陈述为：

```lean
∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
  (w : ClassicalSolutionR ν a f T) (b : ℝ), b ∈ Ico (0 : ℝ) T →
  ∀ L : ℝ, ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) L →
    ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f
```

这是把两个实际经典解沿时间平移拼成原问题延拓的寿命结论，不是范数估计、
统一时间或端点正则性的打包假设。本 lane 尚未构造这个并区间上的经典解及
兼容压力规范。A02 的 `patch` 只处理同初值、同外力且都从零时刻开始的解，
因此不能直接使用；新增 `shiftedSolution` 解决了重叠区间比较，尚不等于拼接。
所有 `…_of_memForceR` 延拓推论仍显式带这个输入，不能称为无条件延拓定理。

消费者没有需要跨外力统一的步骤。必要的 V2 改动是 f、S 在 δ 之前固定，
初值界改用 Grönwall 已提供的 H⁷；不能保持旧 R1 的全部量词与 H¹ 假设而只
换名字。本 lane 不替 owner 决定或修改合同。具名缺口对一般非零解也是
标准的内部重启拼接要求，不要求不可取得的终点载体；审计另给实际零解实例。

## 4. 跑了什么命令、什么结果

所有 Lean 命令先 `. scripts/lean-env.sh`，Lake 均从 `verification/`
执行，`LEAN_NUM_THREADS=6`。工作仅在本 worktree；没有 push、merge、rebase。

- `lake -q --log-level=error build NSFormalization.Section4.A04.RestartFixedForce`：通过，零输出。
- `lake env lean ../formalization/NSFormalization/Section4/A04/RestartFixedForce.lean`：通过，零输出。
- `lake env lean ../research/A04/axioms_restart_fixed_force.lean`：通过；16 个声明均恰为 `[propext, Classical.choice, Quot.sound]`；`HigherOrderBound` 的逐字形状等式和三个实际零解实例通过。
- 根目录 `make check`：通过，含合同政策的 13 项测试和 30 项工作队列检查。
- `lake test`：通过；这是在 verification 中执行 Makefile 合同测试目标的等价调用。
- `python3 experiments/test_contract_mutations.py --skip-build`：通过，三种违规变异按预期拒绝。
- `git diff --check`：通过。生产模块没有占位证明、新增公理、`native_decide` 或心跳调整。

完整门禁日志保留在 worktree 的 `tmp/*_215.log`，不把原始日志复制进记录。
