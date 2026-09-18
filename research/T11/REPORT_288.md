# 288-SPEC-t11-draft-a 报告

## 1. 规范了哪个定理

完成了 `prop:local` 在 `T³` 上的双盲草案 A：对每个 `ν>0`、
`a∈X_T`、`f∈F_T`，陈述同一个正局部区间上的全阶 Sobolev 光滑性、
周期压力 Poisson 方程与零均值规范、共同区间唯一性、最大寿命解；并逐字覆盖
`eq:criterion`
`∫₀^S ‖u(t)‖²_{H²(T³)}dt<∞` 的具体延拓结论。Appendix A 的 `H¹`
统一重启、全阶 Grönwall 界、Galilean 均值消去和正黏性到单位黏性的双向重标度
也分别成为了具体接口。这里交付的是无证明的规范陈述，不声称已证明这些分析
结论。

## 2. Lean 里现在有什么

- `DraftA.lean` 以 T10 相同的两个 import 开头，只逐字复制实际使用的 T10
  声明；每份副本都标了原始行号和注册 `T01.torus_data` 后删除的说明。
- `PeriodicLocalRegularity` 陈述同一 `[0,T)` 上的全阶 Fourier-Sobolev 时间
  光滑、投影方程、周期压力 Poisson 方程、空间周期性和 `∫p=0`。
- `PeriodicLocalTheoryAPI` 给出命名 horizon、局部解、正则性、共同区间速度/规范
  压力唯一性，以及以一对共同物理场表示的 `PeriodicMaximalSolution`。
  最大寿命保持为 `ℝ≥0∞`；没有把 `⊤` 或有限端点伪装成
  `ClassicalSolutionT` 所要求的实数 horizon。
- `PeriodicContinuationAPI` 用 `ℝ≥0∞` 的 `lintegral` 表示平方 `H²` 判据。
  `extendsBeyond` 返回严格更长 horizon 上的真实 `ClassicalSolutionT`，并在
  `[0,S)` 上逐点保持速度和零均值压力；另有 manuscript-strength `H¹` restart、
  高阶界、统一 restartBeyond 和最大寿命无穷推论。
- `PeriodicMeanReductionAPI` 明确给出 `m`、`X`、`v`、`h`、平移压力，陈述
  `m'=mean(f)`、变换后方程、速度/力均值为零及平移 Sobolev 等距。
- `PeriodicViscosityRescalingAPI` 陈述 Appendix A 的 `τ=νt` 正向单位黏性变换
  和逆变换。
- `COMPARISON_A.md` 给出了 paper clause → Lean field → A01/A02/A04 对应字段表，
  记录表示选择、歧义、证明债和现有 `Paper1/Periodic*` 实现候选。

## 3. 缺口是什么

这条 lane 只负责 statements。主要证明缺口是：T10 注册；真正的周期 Fourier
局部理论与同一全阶区间；压力 Poisson/零均值恢复；共同区间唯一性与最大解拼接；
平方 `H²` `lintegral` 的可测性和高阶能量/Grönwall；manuscript 的定量 `H¹`
重启；时间平移后不再属于 `F_T` 的更大局部理论力类；Galilean 变换的均值 ODE、
平移等距和 PDE 抵消；黏性重标度的链式法则。完整逐项列表在
`COMPARISON_A.md` §4。

一个需要 reconciliation 明确保留的类型事实是：`timeShiftT t₀ f` 在新时间零点
可以非零，因此一般不属于 T10 的 `forceClassT`。所以 restart 直接返回 shifted-force
解，而没有错误地调用只接受 `F_T` 的命名 horizon。另一个待裁决点是压力 Poisson
方程是否在 `t=0` 也作为恢复公式陈述；草案 A 取 `Ico 0 T`，与一侧光滑和“pressure
is recovered from”一致。

## 4. 跑了什么、结果如何

- `cd verification && lake env lean ../research/T11/DraftA.lean`：通过，退出码 0，
  无输出。
- `git diff --check`：通过，无输出。
- `rg` 审计 `sorry|admit|axiom`：新 T11 文件无命中。唯一出现的证明块是按简报
  要求逐字复制的 T10 `realPeriodicSubmodule` 结构字段实现；T11 新增接口本身没有
  proof、`sorry`、`admit` 或新公理。
