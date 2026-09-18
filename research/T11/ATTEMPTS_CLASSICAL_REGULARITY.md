# ATTEMPTS — lane 339, T11 unit U6b (`Section3/T11/ClassicalRegularity.lean`)

目标：`∀ ν > 0, ∀ a ∈ initialClassT, ∀ f ∈ forceClassT, ∀ T (w : ClassicalSolutionT ν a f T),
PeriodicLocalRegularity ν a f T w`。**无命名输入，三条子句全部证完。**

## 1. `sobolev_smooth`：走过的路与被否掉的路

| 路线 | 结论 |
|---|---|
| 直接对 `ClassicalSolutionT.sobolev` 给出的 `G` 求导 | **不行**。`sobolev` 只给 `ContinuousOn G (Ico 0 T)`；`ContDiffOn ℝ ∞ G` 要的是 `lp` 值路径的各阶导数，结构体里没有。 |
| 只在 `Ioo 0 T` 上做 | **不行**。`ContDiffOn ℝ ∞ G (Ico 0 T)` 的内容全在 `Ico 0 T` 上，`t = 0` 处需要真正的单侧导数；`G` 在集合外的取值不受约束但也进不了结论。 |
| 用 `∂ₜu = νΔu − (u·∇)u − ∇p + f` 把高阶时间导数换成空间导数 | 放弃：对流项需要乘积估计（U12b 未落地），而且要对导数阶数归纳，控制会爆。 |
| 差商场的 `H^m` 范数 ≤ sup 范数（Bernstein）+ 一致收敛 | **半成品**。需要 `L^[N]`（迭代 Laplace）对"差商"线性，即 `L^[N]` 在 C^∞ 上的加法/数乘性，要对 N 归纳、每步带可微性，代价不小。 |
| **采用**：系数逐点求导 + 紧窗一致加权界 + Tannery | 成立。见下。 |

最终路线的四块：

1. **Bernstein 界**（`weight_pow_mul_norm_coeff_le`）：对光滑周期复值 `g`，
   `W(k)^N‖ĝ(k)‖ ≤ 2^N (sup_cube|g| + sup_cube|Δ^N g|)`，其中 `W(k) = 1 + 4π²|k|²`。
   证法：`periodicFourierCoeff_laplacian` 迭代给 `(Δ^N g)^(k) = (−4π²|k|²)^N ĝ(k)`；
   `‖ĝ(k)‖ ≤ sup_cube|g|`（概率测度，用 335 的 `norm_periodicFourierCoeff_le_of_cube_bound`）；
   再用 `(1+A)^N ≤ 2^N(1+A^N)`（`A ≥ 0`，按 `A ≤ 1` / `A ≥ 1` 分情形）。
   **关键点**：这里只需要"同一个场"的界，不需要 `L^[N]` 对差商线性——这正是上表第 4 行被绕开的原因。
2. **时空导数场**。`stPartial j F z := fderiv ℝ (fun y ↦ F (z.1,y)) z.2 eⱼ`（冻结时间的空间导数，
   在闭端 `t = 0` 处也是普通 `fderiv`，无需开集）；`stTime T F z := fderivWithin ℝ F (slabT T) z (1,0)`
   （**在 slab 内**求时间导数，所以在 `t = 0` 有定义且联合光滑）。两者都保持
   `ContDiffOn ℝ ∞ · (slabT T)` 与 `IsPeriodicOn (Ico 0 T)`；周期性由一条公共引理
   `fderivWithin_slabT_periodic`（平移 `z ↦ z + (0,eᵢ)` 保 slab，`HasFDerivWithinAt.congr` + 唯一性）给出。
   踩过的坑：写 `ContinuousLinearMap.inr ℝ ℝ Space` 会与 `Space` 的 `PiLp`/`WithLp` 实例路径对不上
   （`Application type mismatch … PiLp.normedAddCommGroup … vs WithLp.instAddCommGroup`）；
   改成 `have h : HasFDerivAt (显式函数) _ 点 := 复合` 让 Lean 自己填导数即可。
3. **紧窗一致界**（`SlabSmooth.exists_coeff_bound`）：`J ×ˢ cube` 紧 + `Φ` 与 `stLaplace^[m+2] Φ` 在 slab 上连续
   ⇒ `∃ D, ∀ s ∈ J, ∀ i k, W(k)^{m+2}‖û ᵢ(s,k)‖ ≤ D`。三个分量的常数取和（`Finset.single_le_sum`）。
4. **Tannery**（`tendsto_norm_zero_of_entries`）：`‖A‖² = ∑ᵢ ∑'ₖ ‖A i k‖²`
   （`PiLp.norm_sq_eq_of_L2` + `lp.hasSum_norm`），逐项收敛 + 控制函数 `D²·W(k)⁻²`
   （`summable_inverse_periodicFrequencyWeight`）⇒ `Mathlib.Analysis.Normed.Group.Tannery` 的
   `tendsto_tsum_of_dominated_convergence`。一个权重被 `weight_entry_le` 吸收：
   `W·W^{m/2} = W^{1+m/2} ≤ W^{m+2}`（`W ≥ 1`，`Real.rpow_le_rpow_of_exponent_le`）。

内部时刻的导数：335 的 `hasDerivAt_velocityCoeffT` 给逐系数导数；对差商的一致界用中值不等式
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`（在 `Icc (t−ε) (t+ε) ⊆ Ioo 0 T` 上）。
`t = 0` 处用 `Mathlib.Analysis.Calculus.FDeriv.Extend` 的 `hasDerivWithinAt_Ici_of_tendsto_deriv`
（内部可微 + 端点连续 + 导数有极限 ⇒ 单侧可导）。
最后对求导阶数归纳：`contDiffOn_infty` + `contDiffOn_succ_iff_derivWithin`（`uniqueDiffOn_Ico`），
第 `j` 阶导数就是 `stTime^[j] u` 的数据路径（`hasDerivWithinAt_datumPathT` + `HasDerivWithinAt.derivWithin`）。

## 2. `pressure_poisson`：两处非平凡

* `div(∂ₜu) = ∂ₜ(div u) = 0`：二阶导数对称性。`Transport.spatialDivergence_directional_eq_zero`
  只覆盖**空间**方向，时间方向要自己做：在**开** slab 上取 `F' = fderiv ℝ u`、`F'' = fderiv ℝ F' (t,x)`，
  `ContDiffAt.isSymmSndFDerivAt`（`minSmoothness ℝ 2 ≤ ∞`）给 `F'' v w = F'' w v`；
  `g z := ∑ᵢ (F' z (0,eᵢ))ᵢ` 在开 slab 上恒为 0，故 `HasFDerivAt g 0`，与逐项链式法则得到的导数比较，
  在 `(1,0)` 上求值即 `∑ᵢ (F''(1,0)(0,eᵢ))ᵢ = 0`；再用对称性换成 `∑ᵢ (F''(0,eᵢ)(1,0))ᵢ`，正是 `div(∂ₜu)`。
* `div(Δu) = 0`：把 331 的 `spatialDivergence_directional_eq_zero` **用两次**（第二次作用在
  `z ↦ spatialDerivative u z.1 z.2 eᵢ` 上，它的散度由第一次给出为 0），再对 `i` 求和
  （`divSpatial_sum`）。这样完全不必碰三阶导数的对称性。
* **时刻 0**：目标子句在 `Ico 0 T` 上，而动量方程只在 `Ioo 0 T` 上。三项
  （`scalarSpatialLaplacianT p`、`spatialDivergence f`、`spatialDivergence (∇·(u⊗u))`）都用
  `stPartial` 写成 slab 上的 `ContDiffOn`，因此对 `t` 在 `Ico 0 T` 上连续；
  `𝓝[>]0` 上恒等式成立 + 极限唯一 ⇒ `t = 0` 也成立。

## 3. 其它踩过的小坑

* `dif_pos` 在 v4.34.0-rc2 已弃用（`LESSONS.md` 首条）：`datumPathT_spec` 改用 `unfold` + `split_ifs`。
* `DifferentiableAt.const_smul` 给出的是 `c • f`（Pi 数乘）而不是 `fun y ↦ c • f y`，`rw` 对不上模式；
  先 `have : DifferentiableAt ℝ (fun y ↦ c • g y) x := hg.const_smul c` 再用。
* `ContinuousOn.sum` 不存在，用 `continuousOn_finsetSum`；`contDiff_finset_sum` 不存在，用 `ContDiff.sum`。
* `ContinuousLinearMap.sum_apply` / `zero_apply` 已迁出命名空间（用裸 `sum_apply` / `zero_apply`）；
  `EuclideanSpace.proj_apply` 不存在。
* `ContDiff.fderiv_right` 的目标光滑度若不被结果类型钉住会留下 `?m = ω` 的副目标；
  用带类型标注的 `have` 固定。
* `linarith` 不会把 `spatialDivergence f t x` 与 `divSpatial (fun y ↦ f (t,y)) x` 当成同一个原子
  （两者 `rfl` 相等）；收尾前用 `show` 把目标改写成 `divSpatial` 形式。

## 4. 残留

无。三条子句均无条件；`to_unit` / `from_unit` / `transformed_solution` 与 `regularity_of_solution`
随之无条件。唯一仍未闭合的邻接项是 U12b 的配对估计（与本单元无关）。
