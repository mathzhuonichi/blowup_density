# Lane 289 报告 — T11 periodic local theory / continuation draft B

## 1. 规范了哪个定理

本 lane 给出了 `prop:local` 在 `T³` 上的独立 draft B 陈述：对
`ν>0`、`a∈initialClassT`、`f∈forceClassT`，同一个正时间区间上存在所有
Sobolev 阶都光滑的周期经典解；速度在公共区间唯一，零均值规范后的压力
逐点唯一；局部解拼成唯一最大解。另逐字落实 `eq:criterion`：若实数
`S>0` 且 `∫⁻₀ˢ ‖u(t)‖²_{H²(T³)}<∞`，则存在 `δ>0` 和定义到
`S+δ` 的经典解，并在 `[0,S)` 上同时同意旧速度与规范压力。Appendix A
的固定力 H¹ 重启、高阶 Grönwall 界、周期均值的 Galilean 消去以及粘性
重标度也各自成为具体结构字段；本 lane 只写规范，没有声称证明这些字段。

## 2. Lean 里现在有什么

`research/T11/DraftB.lean` 使用与 T10 相同的两个 import，并只在
`BlowupDensity.T10.Draft` 中逐字复制实际使用的 T10 声明，每段都标了来源行
和注册后删除说明。新命名空间 `BlowupDensity.T11.DraftB` 中包含：

* `PeriodicLocalRegularity`、`PeriodicLocalTheoryAPI`；
* `IsMaximalPeriodicSolution`，以一个公共 `(u,p)` 在每个严格短于
  `ℝ≥0∞` 最大寿命的实数区间上的限制表达最大性；
* `PeriodicContinuationAPI`、`squaredHTwoIntegralT`、`ExtendsBeyondT`；
* `PeriodicMeanReductionAPI` 及完整 Galilean 变换定义；
* `PeriodicViscosityRescalingAPI` 及正反缩放定义。

所有新增结构字段都有论文行号、精确量词顺序和 non-vacuity 说明；没有
占位 `Prop`。`COMPARISON_B.md` 给出论文条款、T11 字段和
`A01.*`/`A02.*`/`A04.*` 对应字段的逐项表，并记录了表示选择、歧义、所需
引理和现有 `Paper1/Periodic*` 候选。

## 3. 还缺什么

本 draft 的主要证明债是：T10 注册与结构体双向转换；周期 Leray 图和压力
Poisson 公式的等价；所有阶 Fourier datum 路径的时间光滑性；规范解的限制、
重叠唯一性与最大粘合；`lintegral` 版 H² 判据和现有
`FiniteH2Energy` 的桥；高阶能量/Gronwall 与固定力 H¹ 重启；均值微分、平移
等距、Galilean 链式法则；粘性缩放的类保持和正反解转换。现有
`PeriodicLocalLifespan.ClassicalPeriodicLocalTheory` 是最接近的条件接口，
但其 `Flow` 与 T10 `ClassicalSolutionT` 是不同结构，按结构体例外必须逐字段
转换。仓库中没有 `PeriodicMeanReduction*` 或 `Galilean*` 实现文件。

## 4. 跑了什么、结果如何

在 `verification/` 下运行：

* `lake env lean ../research/T11/DraftB.lean`：通过，退出码 0；
* `make check`：通过；检查器仍报告仓库已知的
  `Paper1/BoundaryCorollary.lean:90` `sorry` 和 source-hash 差异，本 lane
  未引入或修改它们；
* `make test`：通过；只有既有依赖的 linter warning；
* `make test-mutations`：通过，四类 mutation 结果符合预期；
* `git diff --check`：通过；
* 对交付文件检查 `sorry` / `admit` / `axiom`：Lean 文件无命中
  （比较文档中的英文动词 “admit” 不是 Lean 占位）。
