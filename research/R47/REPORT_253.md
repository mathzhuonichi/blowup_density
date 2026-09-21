# Lane 253 — R47 spatial flux cancellation

## 1. 证了哪个定理

`compactMomentumIntegral` 无条件关闭 lane 251 的唯一具名输入：对任意实际
R42 记录、`ε ∈ (0,ε₀]`、包含插入球的网格 cell 和 `0<t<T`，两条动量残差之差
在 cell 的积分等于速度差时间导数的全空间积分。

`forceDifference_cell_integral_zero'`、`force_gridObservation_eq'` 因而覆盖
整个 `[0,T)`；观测结论仅保留原 R47 假设 `hg : MemForceR A.g`。

## 2. Lean 里现在有什么

新增 `verification/Bindings/FluxCancellation.lean`，12 个定理。紧支撑向量
方向导数通过与常数 1 分部积分得到零均值；对流项用两条速度的无散条件写成
张量差的散度；压力项和黏性项分别使用紧压力差与紧速度差的导数。

实际动量方程把残差差识别为紧力差，从而证明可积性并把 cell 积分换成全空间
积分；此处没有使用力差零均值。随后逐项消去空间通量。时间项零均值与零时刻
处理复用 lane 251。当前 R42 字段已选紧压力规范；另证明了任意空间常数
`c(t)` 不改变压力梯度。

新增审计 `research/R47/axioms_flux_cancellation.lean`：12 个声明全部恰好
依赖 `[propext, Classical.choice, Quot.sound]`，四个非空洞应用探针通过。
证明路线、精确类型、失败尝试见 `ATTEMPTS_FLUX.md`。没有提高默认心跳限制。

## 3. 缺口是什么

本 lane 目标无剩余分析输入。未装配完整 R47 `RGridFamily` 或修改合同注册；
这些不属于本 lane。`hg` 是原定理的背景力条件，不是新增分析缺口。
仅新增四个交付文件，未修改 lane 251 或任何既有文件；未 push、merge、rebase。

## 4. 跑了什么命令、什么结果

先加载 `. scripts/lean-env.sh`，全部 Lake/Lean 命令在 `verification/` 下、
`LEAN_NUM_THREADS=6`：

- `lake build Bindings.FluxCancellation`：通过；新模块无 warning，完整构建日志
  有既有依赖的 replay warnings，未宣称整个依赖树静默。
- `lake env lean Bindings/FluxCancellation.lean`：通过，0 字节输出。
- `lake env lean ../research/R47/axioms_flux_cancellation.lean`：通过，12 条
  公理输出均为规定三个公理，四个 example 通过。
- 根目录 `make check`：通过。
- `lake test`（在 verification 内执行的合同测试）：通过。
- `make test-mutations`：通过，三个变异均按要求拒绝。
- `python3 experiments/check_contracts.py --base-ref HEAD`：相对本 lane 实际
  起点通过兼容性检查；不以已前移的远端集成引用替代实际起点。
- `git diff --check`：通过。
