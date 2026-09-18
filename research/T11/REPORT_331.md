# REPORT 331 — T11/U6 solution transport (`Transport.lean`)

## 1. 证了哪个定理（what is proved）

**一个通用输运构造器**，把 `(t,x) ↦ (α t, x + X(t))`（`X : ℝ → Space` 为 `C^∞`，`c = X'`,
`d = X''`，常数 `α > 0`）下的变换解重建成一个 `ClassicalSolutionT`：

`Transport.classicalSolutionT_transport`
(`w : ClassicalSolutionT ν a f T`, `hα : 0 < α`, `α T' = T`, `ν' = α ν`,
`hv : ∀ t x, v (t,x) = α • w.velocity (α t, x + X t) - c t`,
`hq : ∀ t x, q (t,x) = α² * w.pressure (α t, x + X t)`,
`hg : ∀ t x, g (t,x) = α² • f (α t, x + X t) - d t`,
`ha' : ∀ x, a' x = α • a (x + X 0) - c 0`) `: ClassicalSolutionT ν' a' g T'`

**14 个字段全部证明**，无 `sorry`、无公理、无命名输入：光滑性（与 `Φ(z) = (α z.1, z.2 + X z.1)`
复合 + `MapsTo`）、初值、散度（`spatialDivergence_slice`）、动量（`navierStokesResidual_transport`：
时间导数的输运项 `α (D_xu)(X'(t))` 与平移速度的多余对流项精确抵消，粘性变为 `α ν`，残差整体是
`α²` 倍并平移 `-X''`）、Sobolev 数据路径（平移特征子 × 幅度 × 零模常数，含 `lp` 范数下的强连续性）、
压强梯度 `MemLp`、两条周期性、压强规范（Haar 平移不变性）。

三次实例化：

* `classicalSolutionT_galilean` — `α = 1`, `X = galileanShiftT a f`, `c = galileanMeanT a f`,
  `d = forceMeanT f`（FTC 给出 `HasDerivAt`）：给出
  `ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T`，且
  `.velocity = galileanVelocityT a f w.velocity`、`.pressure = galileanPressureT a f w.pressure`
  都是 `rfl`；
* `classicalSolutionT_toUnit` — `α = ν⁻¹`, `X = 0`：`ClassicalSolutionT 1 (unitViscosityInitialT ν a)
  (unitViscosityForceT ν f) (ν * T)`；
* `classicalSolutionT_fromUnit` — `α = ν`：逆向，`ClassicalSolutionT ν a f T`。

局部正则性：`periodicLocalRegularity_toUnit` / `periodicLocalRegularity_fromUnit` 把源解的
`PeriodicLocalRegularity` 完整输运（三条子句）；Galilean 情形证了其中两条
（`pressure_poisson_galilean`、`classicalSolutionT_projected`）。

API 形状的结论（`research/T11/probes/api_on_canonical.lean` 的字段原文）：

* `to_unit_of_regularity`、`from_unit_of_regularity` = 目标字段原文 + 一个额外假设
  （**所给解**的 `PeriodicLocalRegularity`）；
* `transformed_solution_fields` = `transformed_solution` 去掉正则性合取项，**无条件**；
* `transformed_solution_two_clauses` = 再加上 `pressure_poisson` 与 `projected` 两条子句
  （条件同上）。

## 2. Lean 里现在有什么

新模块 `formalization/NSFormalization/Section3/T11/Transport.lean`（1282 行，命名空间
`NSFormalization.Section3.T11.Transport`，72 个声明，全部 `#print axioms` 恰为
`[propext, Classical.choice, Quot.sound]`）：

* §1–§3b 冻结时间的链式法则：`spatialDerivative_slice`、`spatialDivergence_slice`、
  `spatialLaplacian_slice`、`pressureGradient_slice`、`scalarSpatialLaplacianT_slice`、
  `advection_slice`、`convectionDivergence_slice_smul`、`temporalDerivative_line`
  （多变量链式法则，含 `-Ẋ(t)` 输运项）、`navierStokesResidual_transport`；
* §4 数据输运：`translateCoeff`（`e^{2πi k·y}`）、`translateScalarData`、
  `translatePeriodicDatum` 及范数不变性、`periodicFourierCoeff_translate`、
  `isPeriodicDatum_translate`、`constantDatum` 及其 `IsPeriodicDatum`/范数/连续性、
  `isPeriodicDatum_smul`、`isPeriodicDatum_transport`，以及平移族在 `ℓ²` 中的**强连续性**
  `continuous_translateScalarData` / `continuous_translatePeriodicDatum` /
  `continuous_translate_pair`（Tannery 定理，控制函数 `4‖A k‖²`）；
* §5–§6 slab 工具与构造器本体；§7 两个粘性实例；§7b/§7c 正则性输运，含
  `spatialDivergence_directional_eq_zero`（二阶导数对称性：`div (D_c u) = D_c (div u) = 0`）
  与 `pressure_poisson_translate` / `pressure_poisson_rescale`；§8 Galilean 实例（FTC 引理
  `hasDerivAt_intervalPrimitive`、`contDiff_intervalPrimitive`、`galileanShiftT_zero` 等）；
  §9 API 形状结论。

探针 `research/T11/probes/transport_closes.lean`：三个目标字段原文（`to_unit`、`from_unit` 带
唯一残余假设；`transformed_solution` 的无条件部分与两子句版本），加非平凡性——常值流
`constantFlow ν`（14 个字段全证）在 `ν = 2` 下 `w.velocity (0,0) = e₀ ≠ 0`，其单位粘性重标
速度 `2⁻¹ • e₀ ≠ 0`，其 Galilean 变换速度在 `(0,0)` 恰为 `0`（均值被减去）。

审计 `research/T11/axioms_transport.lean`：72 条 `#guard_msgs` + `#print axioms`。

## 3. 缺口是什么（exact residual statements）

**唯一残余**（探针里写成显式假设，不是模块里的命名输入）：

```
∀ (ν : ℝ), 0 < ν → ∀ a ∈ initialClassT, ∀ f ∈ forceClassT,
  ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T), PeriodicLocalRegularity ν a f T w
```

即「每个经典周期解都满足 `PeriodicLocalRegularity`」。目标字段 `transformed_solution`、
`to_unit`、`from_unit` 对**任意** `ClassicalSolutionT` 量化，而该结构的 `sobolev` 字段只给出
`ContinuousOn G (Ico 0 T)`，`PeriodicLocalRegularity.sobolev_smooth` 要的是
`ContDiffOn ℝ ∞ G (Ico 0 T)`（`lp` 值路径）。树里没有任何声明给出 `C^∞` 数据路径
（`T10.ForcePaths.continuous_datum_path` 只到连续，且要求全时空 `ContDiff`），所以这条正则性
无法凭空产生——它属于 U9/U9d 的存在性构造（那里解是带正则性造出来的）。

第二个（只影响 Galilean 字段的条件版本）：**平移族在 `H^m` 中不可微**。
`t ↦ T_{X t} A` 的形式导数把系数乘以 `2πi (k·X'(t))`，落在 `H^{m-1}`；要证
`ContDiffOn ℝ ∞ (fun t ↦ T_{X t}(G_m t) - constantDatum (c t))` 需要所有阶的路径 + 乘子
`H^{s+1} →L H^s` + 对可微阶数的归纳，是独立的一个单元。两个粘性实例 `X = 0`，不受影响，
`periodicLocalRegularity_toUnit/_fromUnit` 已完整。

其余没有缺口：`ClassicalSolutionT` 层面的三次输运都是**无条件**的。

## 4. 跑了什么命令、什么结果

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Transport
  → Build completed successfully (9949 jobs)，Transport.lean 零 error 零 warning
lake env lean ../formalization/NSFormalization/Section3/T11/Transport.lean   → 无输出
lake env lean ../research/T11/probes/transport_closes.lean                    → 无输出
lake env lean ../research/T11/axioms_transport.lean                           → 无输出（72 条 #guard_msgs 全过）
make check（worktree 根）  → plan/contracts/policy(13 tests)/work queue 全过
make test                  → 已注册合同闭包全部 "standard logical axioms only"
```
