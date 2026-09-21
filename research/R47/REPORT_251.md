# Lane 251 — R47 force cell integral

## 1. 证了哪个定理

`velocityDifference_cell_integral_zero` 及分量版本：对任意实际 R42 记录、
`ε ∈ (0,ε₀]`、`t ∈ [0,T)`，只要插入球包含于网格 cell，速度差在该 cell
的积分为零。另无条件证明了内点时间的速度差时间导数之全空间积分为零。

`forceDifference_cell_integral_zero` 和力观测相等覆盖 `[0,T)`，但仍条件于
下述唯一空间通量积分输入；**没有声称无条件闭合 eq:gridforce**。
零时刻的力差及全部力观测相等无条件成立。

## 2. Lean 里现在有什么

新增 `verification/Bindings/ForceCellIntegral.lean`，14 个定理。
速度侧使用 R42 的光滑性、支撑、无散字段和
`Paper3.setIntegral_component_eq_zero`；时间项使用
`Paper3.integral_timeDerivative_component_eq_zero`，在紧时间窗口
`[t/2,(t+T)/2]` 上以固定闭球控制支撑。

`insertion_momentum_difference` 从 `A.momentum` 和 `A.reference.momentum`
直接相减，并用 reference 的速度/压力等式对齐载体。
`velocity_gridObservation_eq`、`force_gridObservation_eq` 调用 lane 247 的
`gridObservation_locality`；半开 cell 的可积性由连续性与紧坐标盒证明。
力观测另使用 R47 的原始假设 `hg : MemForceR A.g`，该假设不在裸 R42 记录中。
这些逐网格结论可对 spec 中每个 `containingCell i` 应用；未装配完整 RGridFamily。

审计文件为 `research/R47/axioms_force_cell_integral.lean`，包含 4 个探针：
实际记录的正尺度/内点时间、初始力观测、连续常量场可积性、内点时间导数积分。
14 个声明全部恰好依赖 `[propext, Classical.choice, Quot.sound]`。

## 3. 缺口是什么

唯一未证明的分析输入 `hcompactMomentumIntegral` 精确要求：对每个可用尺度、
包含插入球的 cell `C` 和 `0<t<T`，

```
∫_C [Residualν(uε,pε) − Residualν(v,π)]
  = ∫_R³ deriv (s ↦ uε(s,x) − v(s,x)) t.
```

这是空间通量抵消及紧支撑时间项的积分区域转换；不是力观测相等假设。
时间微分与零均值已在 Lean 中证明，不包含在此输入中。
剩余工作是把非线性差写成 `div(uε⊗uε−v⊗v)`，加上紧压力梯度和黏性项，
逐项调用已有紧支撑空间导数积分为零的引理。

`ATTEMPTS_FORCE_CELL.md` 给出精确 Lean 类型、所需 R42 字段、非平凡插入族的
可满足性论证及失败路线。该输入不要求零时刻双侧光滑，也不要求穿越爆破时刻
的光滑性。没有给它添加公理，也没有声称探针已经构造了这个未证明输入。
遵守仅新增文件约束；后续工作及交接记录放在本报告，不修改 NEXT_SESSION。

## 4. 跑了什么命令、什么结果

均先加载 `. scripts/lean-env.sh`，Lean/Lake 在 `verification/` 下、
`LEAN_NUM_THREADS=6`：

- `lake build Bindings.ForceCellIntegral`：通过；构建日志含既有上游 replay
  warnings，新模块无 warning。
- `lake env lean Bindings/ForceCellIntegral.lean`：通过，0 字节输出。
- `lake env lean ../research/R47/axioms_force_cell_integral.lean`：通过，
  14 个声明均为规定的三个公理，4 个 example 通过。
- 根目录 `make check`：通过。
- `lake test`（`make test` 的 verification 内等价命令）：通过。
- `python3 experiments/test_contract_mutations.py`：通过。
- `git diff --check`：通过。
- 额外兼容性检查 `--base-ref origin/erenup/integration`：失败，原因是该远程
  跟踪引用已领先本车道基线，新增了本基线没有的
  `verification/Contracts/V1/MainThresholds.lean`，检查器将其判作删除。
  `git ls-tree HEAD` 确认该文件本来就不存在。
  对实际基线/merge-base `b2db3263d9e85fdf6282a35557c515f2176579f4`
  的同一兼容性检查通过。没有 merge、rebase 或修改既有合同来掩盖此差异。
