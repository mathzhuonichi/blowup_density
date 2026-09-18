# REPORT — lane 339, T11 unit U6b：每个经典周期解都有论文的局部正则性

## 1. 证了哪个定理（which theorem is proved）

`paper/sections/02-preliminaries.tex:28-36,75-115`（prop:local）在环面上的正则性记录，对**任意**
`ClassicalSolutionT`、**无任何命名输入**：

```lean
theorem periodicLocalRegularity_of_classical : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T), PeriodicLocalRegularity ν a f T w
```

（更强的形式 `periodicLocalRegularity_of_classical'` 只要求 `ContDiff ℝ ∞ f`，不要求类成员资格。）

这正是 **lane 331 的唯一残余**（`REPORT_331.md` §3）与 lane 321 `regularity` 字段的缺口。三条子句：

* `sobolev_smooth`：对每个 `m : ℕ`，速度切片的 `H^m` Fourier 数据路径 `t ↦ datumPathT m u t` 在
  `[0,T)` 上 `ContDiffOn ℝ ∞`（`ℓ²` 值路径，含 `t = 0` 的单侧各阶导数）。
  `ClassicalSolutionT.sobolev` 只提供 `ContinuousOn`，所以这是真正新的分析。
* `pressure_poisson`：`Δp = ∇·f − ∇·(∇·(u⊗u))` 在 `Ico 0 T` 上（动量方程只在 `Ioo 0 T` 上，
  端点靠连续性）。
* `projected`：320 的 `classicalSolutionT_projected` 原文。

随之**无条件**成立的目标字段（`research/T11/probes/api_on_canonical.lean` 原文）：
`PeriodicViscosityRescalingAPI.to_unit`、`.from_unit`、`PeriodicMeanReductionAPI.transformed_solution`，
以及 `PeriodicLocalTheoryAPI.regularity` 的形状 `regularity_of_solution`（对**任意**被选中的
`horizon`/`solution` 族，正则性自动成立）。

## 2. Lean 里现在有什么（what is in Lean now）

新模块 `formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean`（1212 行，82 个声明，
全部 `#print axioms` 恰为 `[propext, Classical.choice, Quot.sound]`，无 `sorry`/`axiom`/
`native_decide`，无 `maxHeartbeats` 覆盖，未改动任何既有模块）。主链：

| 声明 | 内容 |
|---|---|
| `scalarLaplace`, `periodicFourierCoeff_scalarLaplace_iterate` | `(Δ^N g)^(k) = (−4π²|k|²)^N ĝ(k)` |
| `weight_pow_mul_norm_coeff_le` | **Bernstein 界** `W(k)^N‖ĝ(k)‖ ≤ 2^N(sup_cube|g| + sup_cube|Δ^N g|)` |
| `slabT`, `stPartial`, `stTime` | slab、冻结时间的空间导数、**slab 内**的时间导数（`fderivWithin`，在 `t=0` 有定义） |
| `contDiffOn_stPartial` / `stPartial_periodic` / `contDiffOn_stTime` / `stTime_periodic` | 两个算子都保持 slab 上的联合光滑与单位空间周期 |
| `hasDerivWithinAt_stTime`, `temporalDerivative_eq_stTime` | `stTime` 逐条时间线求导（端点单侧）；内部与 `temporalDerivative` 一致 |
| `stLaplace`, `stLaplace_iterate_slice` | 时空版空间 Laplace，切片与 `scalarLaplace^[N]` 逐字相同 |
| `norm_sq_eq_sum_tsum`, `tendsto_norm_zero_of_entries`, `tendsto_of_entries` | 数据载体上的 **Tannery**：逐项收敛 + 一条一致加权界 ⇒ `ℓ²` 收敛 |
| `SlabSmooth`, `SlabSmooth.exists_coeff_bound` | slab 光滑周期场；紧时间窗上 `W(k)^{m+2}‖û ᵢ(s,k)‖ ≤ D` 的**一致**界 |
| `datumPathT`, `datumPathT_spec`, `datumPathT_entry` | 切片的 `H^m` 数据（唯一，故由 `IsPeriodicDatum` 完全确定） |
| `continuousWithinAt_datumPathT` | 数据路径在 `[0,T)` 上连续（含 `t = 0`） |
| `hasDerivAt_datumPathT` | 内部时刻可导，导数 = `stTime T u` 的数据路径（中值不等式给一致斜率界） |
| `hasDerivWithinAt_datumPathT` | 端点用 `hasDerivWithinAt_Ici_of_tendsto_deriv` 补上单侧导数 |
| `contDiffOn_datumPathT` | **`ContDiffOn ℝ ∞ (datumPathT m V) (Ico 0 T)`**，对阶数归纳（`contDiffOn_succ_iff_derivWithin`） |
| `divSpatial_*` | 空间散度的线性性、`div ∇p = Δp` |
| `divSpatial_spatialLaplacian_eq_zero` | `div Δu = 0`（把 331 的方向导数引理用两次） |
| `divSpatial_temporalDerivative_eq_zero` | `div ∂ₜu = ∂ₜ div u = 0`（`ContDiffAt.isSymmSndFDerivAt`） |
| `pressure_poisson_interior` / `pressure_poisson_of_classical` | Poisson 方程，先在 `Ioo 0 T`，再由三项对 `t` 的连续性延拓到 `t = 0` |
| `periodicLocalRegularity_of_classical(')` | **主定理** |
| `to_unit`, `from_unit`, `transformed_solution`, `regularity_of_solution` | 四条无条件推论 |

探针 `research/T11/probes/classical_regularity_closes.lean`：主定理 + 三个目标字段原文 +
`PeriodicLocalTheoryAPI.regularity` 形状，全部 `:=` 直接闭合；非平凡性用 331 的常值流
`constantFlow 2`（`u ≡ e₀`，`f = 0`，`[0,1)`）——它拿到完整的 `PeriodicLocalRegularity`，
`w.velocity (0,0) ≠ 0`，且**任何**满足 `sobolev_smooth` 的数据路径 `G` 都有 `G 0 ≠ 0`
（零频分量为 `1`），所以该子句不是被零数据平凡满足的。

审计 `research/T11/axioms_classical_regularity.lean`：82 条 `#guard_msgs` 卡住的 `#print axioms`，
每条恰好三条标准公理。

## 3. 缺口是什么（what is missing）

**本单元没有缺口**，也没有命名输入。三条子句都是无条件定理。

口径说明两条，供 lead 判断：

* `pressure_poisson` 的目标区间是 `Ico 0 T`，而 `ClassicalSolutionT.momentum` 只在 `Ioo 0 T` 上。
  本模块用"三项在闭端 slab 上对 `t` 连续 + `𝓝[>]0` 上恒等 + 极限唯一"补上 `t = 0`。
  这依赖 `velocity_smooth`/`pressure_smooth` 是在 `Ico 0 T ×ˢ univ` 上的 `ContDiffOn`（结构体原文），
  没有额外假设。
* 331 记录的第二个残余（"平移族在 `H^m` 中不可微"）**不再需要**：`transformed_solution` 现在不走输运，
  而是先用 331 的 `transformed_solution_fields` 无条件拿到 Galilean 解 `v`（它本身是一个
  `ClassicalSolutionT`），再对 `v` 直接用主定理。`galileanForceT a f ∈ forceClassT` 由
  `GalileanClasses.transformed_classes` 提供。

邻接的未闭合项仍是 U12b 的配对估计（`REPORT_335.md` §3），与本单元无关。

## 4. 跑了什么命令、什么结果（commands and results）

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ClassicalRegularity
  → ✔ [9998/9998] Built NSFormalization.Section3.T11.ClassicalRegularity, Build completed successfully
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean
  → 无输出（0 error、0 warning）
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/classical_regularity_closes.lean
  → 无输出
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_classical_regularity.lean
  → 无输出（82 条 #guard_msgs 全部通过）
make check（worktree 根）  → plan/contracts/policy(13 tests)/work queue 全过
```
