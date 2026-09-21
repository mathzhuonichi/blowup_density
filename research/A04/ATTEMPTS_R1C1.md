# Lane 160 — A04 R1/C1 continuation adapter

## 1. 证明范围

目标为 `appendix-a-local-theory.tex:147–152` 的统一时间重启，以及
`04-whole-space.tex:129–134` 在有限最大寿命端点的反证。

`Continuation.restartBeyond` 保持 `research/A04/Spec.lean:574` 的结论与量词顺序：
统一的 δ 在 datum、force、S、u、p 之前选取，且结论保留完整 S+δ。
`extendsBeyond` 与 `lifespanInfiniteOfLocallyFinite` 保持该 draft 的数学陈述。
所有结果为下述具名分析输入的条件定理，不是已完成的无条件 continuation API。

## 2. Lean 中新增内容

- `ForceShift.lean`：A02 draft 的 `timeShift` 原样重述；通过 indicator 的 Lebesgue
  积分平移证明正时间平移减小半直线积分；逐个 Sobolev datum 构造平移路径，得
  `forceSobolevENormL1_timeShift_le`。该桥无需 `MemForceR`。
- `Continuation.lean`：原样重述 A04 `SolvesBelow`、`squaredHTwoIntegral`。
  `lifespan_ge_of_solvesBelow` 用已证 A02 supremum 序论。
  `restartBeyond_of_restartAt` 在任意严格下界 c 之上选择
  t₀=(max(0,c.toReal−δ)+S)/2，保留完整 δ；不声称端点有经典解。
- 从 SolvesBelow 提供的正寿命，复用 A02 directed-union 构造 maximal fields。
  通过 `uField_eq` 和短区间解把原来的 H¹ 界移到 maximal velocity。
- `restartBeyond` 消费精确 `A02.MaximalSolutionAPI.restart` 形状和已证 force-tail 桥。
- C1 `extendsBeyond` 取 G3 的 m=1，组合速度上界、F1 紧区间 forcing 上界和 forcing
  L¹ 界为一个有限最大值，再调用 R1。
- C1 全局寿命论证只在有限 T_max 的实数值处使用积分有限性；保留
  `0 < maximalLifespanR`，不把范围扩大到寿命之外。

## 3. 剩余输入和尝试

- `Restart` 是精确的 `research/A02/Spec.lean:550–559`，未在本 lane 证明。
  它包含 A01 存在性、统一局部时间、A02 shifted-problem patch/uniqueness 的责任。
- `HigherOrderBound` 是精确的 `research/A04/Spec.lean:534–543` (G3)，本 lane 未证明。
  当前 Gronwall 模块提供标量积分型估计，不能把这一点写成 G3 已自动完成。
- 因此 R1 只依赖显式 Restart；C1 依赖显式 Restart 和 HigherOrderBound。
- 初步检查未找到现成 force shift 桥；后由半直线 indicator 积分与
  `QuasiMeasurePreserving.restrict` 构造，不再保留额外 force-shift 假设于最终定理。
- draft 的 `BoundedIntoHOne` 在 R1 证明里不需要：精确 A02.restart 只消费全时 L¹ forcing
  上界。保留此参数使结论与冻结前 draft 完全一致，不削弱或改写数学陈述。

## 4. 验证

编译交由指定 Luna high agent；writer 未运行 Lean。ForceShift 已通过。
首轮 ForceShift 错误是 QuasiMeasurePreserving 缺 Measure 命名空间，已修。
首轮 Continuation 在 G3/F1 的 m=1 自然数转实数处发生类型展开超时；
以 `simp only [Nat.cast_one]` 显式规整速度界和 forcing L1 界，未增加心跳上限。
修后验证均通过（Luna high，2026-09-15）：

- `lake build NSFormalization.Section4.A04.ForceShift`：exit 0；新增模块无 warning。
- `lake build NSFormalization.Section4.A04.Continuation`：exit 0，9949 jobs，新模块 8.3s。
- `lake env lean ../research/A04/axioms_r1c1.lean`：exit 0；9 个定理审计均只依赖
  `propext`, `Classical.choice`, `Quot.sound`；4 个真实零解/零平移正例通过。
- 日志：`tmp/compile_A04_ForceShift_fixed2_20260915.log`、
  `tmp/compile_A04_Continuation_fixed_20260915.log`、
  `tmp/probe_A04_axioms_r1c1_fixed_20260915.log`。

探针 `research/A04/axioms_r1c1.lean` 覆盖 force-shift、R1、C1 最终定理。
未修改合同、Tests、registry、论文、vendor、PLAN、NEXT_SESSION 或 CSV；未提交。
