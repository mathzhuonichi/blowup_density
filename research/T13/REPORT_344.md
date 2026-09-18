# Lane 344 报告 — T13 `constant_pos_finite` / `endpoint_zero` / `endpoint_one`

分支 `erenup/344-T13-constant-endpoints`。无命名输入（no named input），三个目标字段全部证完。

## 1. 证了哪个定理

`paper/sections/03-torus.tex:22-98`（`lem:localization`）里三条陈述，逐字对应
`research/T13/probes/api_on_canonical.lean` 的 `LocalizationAPI` 三个字段：

1. **`constant_pos_finite`**（`03-torus.tex:35-39`）
   `∀ s, 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤`，
   其中 `cFrac s = ∫⁻ h : Space, ofReal ‖exp(I·h₀) − 1‖² * fractionalRadialKernel s h`
   就是论文的 `c_s = ∫_{ℝ³} |e^{ih₁}−1|²/|h|^{3+2s} dh`（`ℝ≥0∞` 值，奇点保留为 `⊤`）。
   有限性按论文的两段估计：原点附近分子 `≤ |h|²`，剩下 `∫₀¹ r^{1−2s} dr`（需 `s < 1`）；
   远场分子 `≤ 4`，剩下 `∫₁^∞ r^{−1−2s} dr`（需 `0 < s`）。

2. **`endpoint_zero`**（`03-torus.tex:29,96-98`）
   `∀ c r, 0 < r → closure (ball c r) ⊆ interior fundamentalCube → ∀ f, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →`
   `eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) = eLpNorm f 2 volume`。

3. **`endpoint_one`**（同上）同样条件下
   `gradientENorm (periodize f) (volume.restrict fundamentalCube) = gradientENorm f volume`
   （Hilbert–Schmidt 约定，三个方向导数平方和，不与非齐次 `H¹` 认同）。

两个端点的机制是论文那句 "integration over the single copy of the support"：在闭立方体
`[0,1]³` 上，格点平移项 `n ≠ 0` 全部为零，所以周期化就等于零延拓本身。

## 2. Lean 里现在有什么

新模块 `formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean`
（命名空间 `NSFormalization.Section3.T13`，424 行，35 个声明，无 `instance`）：

* §0 坐标工具：`continuous_spaceCoord`、`abs_spaceCoord_le_norm`、`npow_mul_rpow_of_pos`。
* §1 常数：`norm_exp_sub_one_sq_le_sq` / `_le_four` / `_pos`；径向控制函数
  `cFracRadial s y = min (y²) 4 * y^(-(3+2s))` 及其可积性
  （`integrableOn_cFracRadial_Ioo`、`integrableOn_cFracRadial_Ici`、`integrable_cFracRadial`）；
  逐点控制 `cFrac_integrand_le`；结论 `cFrac_lt_top`、`cFrac_pos`。
* §2 立方体几何：`fundamentalCubeInterior`（开立方体 `(0,1)³`）、`isOpen_…`、
  `isClosed_fundamentalCube`、`measurableSet_fundamentalCube`、`convex_fundamentalCube`、
  `volume_frontier_fundamentalCube`（凸集边界零测），以及
  **`interior_fundamentalCube : interior fundamentalCube = (0,1)³`**（两个方向都证）。
* §3 单份周期化：`latticeVector_zero`、`eq_zero_of_mem_cube`（`n ≠ 0` 的平移在整个闭立方体上为零）、
  `periodize_eq_of_mem_cube`、`periodize_eventuallyEq`（内部点的邻域版，供导数用）、
  `tsupport_subset_cube`、`fderiv_eq_zero_of_notMem_tsupport`。
* §4/§5：`endpoint_zero_eq`、`endpoint_one_eq`，以及与 API 字段逐字同型的
  `constant_pos_finite`、`endpoint_zero`、`endpoint_one`。

探针 `research/T13/probes/constant_endpoints_closes.lean`：
逐字复制 `api_on_canonical.lean` 的 `LocalizationAPI` 结构，三个 `example` 分别用三条定理封口；
`localizationAPI_of_remaining_fields` 把整个六字段记录拼出来（另外三个字段作为显式假设，
只用于"逐字段对型"，模块本身不依赖它们）。非平凡性：`cFrac s = ∫⁻ …` 是 `rfl`；
`cFrac (1/2)` 的实例；显式球 `ball probeCenter (3/8)`（`probeCenter = (½,½,½)`）满足
`closure ⊆ interior fundamentalCube`；显式非零光滑场
`probeField = probeBump • coordinateVector 0`（`ContDiffBump`，`rIn=1/8, rOut=1/4`）
满足两个假设且 `probeField probeCenter ≠ 0`，两个端点等式都在它上面实例化。

公理审计 `research/T13/axioms_constant_endpoints.lean`：35 个声明全部
`[propext, Classical.choice, Quot.sound]`。

## 3. 缺口是什么

* 本车道**不**包含 `LocalizationAPI` 的另外三个字段：`wholeSpace_identity`、
  `torus_identity`、`localization`（lane 345/346）。残留陈述逐字见探针里
  `localizationAPI_of_remaining_fields` 的三个假设 `hWholeSpace`、`hTorus`、`hLocalization`。
* `cFrac_pos` 实际只用到 `0 < s`（`s < 1` 未用）；`cFrac_lt_top` 两个都要。
  字段按原样保留两个前提。
* `endpoint_one` 的 `∀ᵐ` 步骤走的是"立方体去掉内部 ⊆ 凸集边界（零测）"，
  没有走"闭立方体的 δ-邻域"路线（后者也成立，但需要紧致分离论证）。记在
  `ATTEMPTS_CONSTANT_ENDPOINTS.md` §2。
* Mathlib 没有 `lintegral` 版的径向约化；本模块用 Bochner 版
  `integrable_fun_norm_addHaar` + `Integrable.hasFiniteIntegral` 过渡。
  若后续 lane 需要 `IReal` 的径向计算（不只是估计），这一步要重做。
* `ContDiffBump` 只出现在探针里（`Mathlib.Analysis.Calculus.BumpFunction.InnerProduct`），
  模块本身不 import 它。

## 4. 跑了什么命令、什么结果

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.ConstantEndpoints
  → Build completed successfully (9357 jobs); 本模块 0 error 0 warning
cd verification && lake env lean ../formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean
  → 无输出（0 error 0 warning）
cd verification && lake env lean ../research/T13/probes/constant_endpoints_closes.lean
  → 无输出（0 error 0 warning）
cd verification && lake env lean ../research/T13/axioms_constant_endpoints.lean
  → 35 行，全部 [propext, Classical.choice, Quot.sound]
make check（worktree 根目录）
  → OK（结果见提交说明）
```
