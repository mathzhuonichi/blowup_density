# Lane 348 报告 — T13 `wholeSpace_identity`（whole-space Gagliardo/Fourier 恒等式）

分支 `erenup/348-T13-wholespace-identity`。无命名输入、无占位、无 sorry/axiom；
`LocalizationAPI` 的 `wholeSpace_identity` 字段逐字证完。

## 1. 证了哪个定理

`paper/sections/03-torus.tex:40-51`，逐字对应
`research/T13/probes/api_on_canonical.lean:47-51` 的 `wholeSpace_identity` 字段：

```
theorem wholeSpace_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ)
```

其中 `IReal s f = ∫⁻ h, ∫⁻ x, ofReal ‖f(x+h) − f x‖² · |h|^{-3-2s}`，
`cFrac s = ∫⁻ h, ofReal ‖e^{i h₀} − 1‖² · |h|^{-3-2s}`（`Section3/T13/Localization.lean`），
`dotHomogeneousENorm`（`Section4/D01/HomogeneousNorm.lean`）是注册的 Ḣ^s(ℝ³) 数据下确界范数。

证法即论文那句 “change variables y=x+h, then Plancherel and Tonelli”：
角向 Plancherel（酉变换）逐分量、逐 `h`，Tonelli 交换 `h,ξ`，旋转+膨胀把内层
`∫⁻ h |e^{i⟨h,ξ⟩}−1|² |h|^{-3-2s} = c_s |ξ|^{2s}`（`ξ≠0`），并用下确界桥把
`dotHomogeneousENorm` 换成论文的 Fourier 量。有限性来自 344 的 `constant_pos_finite`
与 `homogeneousFourierENorm_lt_top`。

## 2. Lean 里现在有什么

新模块 `formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean`
（命名空间 `NSFormalization.Section3.T13`），关键声明：

- `dotHomogeneousENorm_eq_homogeneousFourierENorm`：下确界桥（光滑紧支）。
- `homogeneousFourierENorm_lt_top`、`homogeneousFourierENorm_sq`：有限性与平方展开。
- `schwartz_lintegral_normSq`、`lintegral_angularFourier_sq`：角向 Plancherel（酉）。
- `angularFourier_translate`、`angularFourier_sub`、`angularFourier_diff`：平移相位与可加性。
- `per_h_component`：逐分量逐 `h` 的物理平方积分 = 频率侧相位加权能量。
- `exists_rotation`（private）、`lintegral_kernel_smul`：旋转+膨胀求内层核积分。
- `measurable_kernel`、`continuous_phase`、`measurable_weightedSq`、
  `continuous_angularFourier_component`、`ofReal_normSq_eq_sum`：测度/连续性辅助。
- `component_integral_eq`：单分量双重积分 = `c_s · ∫⁻ ‖ξ‖^{2s}‖F̂ᵢ‖²`（含 Tonelli + 核缩放）。
- `IReal_decomp`、`IReal_eq_cFrac_mul_homogeneousFourierENorm_sq`：分量分解与主恒等式。
- `wholeSpace_identity`：API 字段（两段结论：有限 + 恒等式）。

探针 `research/T13/probes/wholespace_identity_closes.lean`：`example ... := wholeSpace_identity`
逐字封口；非平凡性用显式 `ContDiffBump` 场 `probeField = probeBump • coordinateVector 0`
（`probeField_ne_zero`、`probeField_hasCompactSupport`）在 `s=1/2` 上实例化整条结论。

公理审计 `research/T13/axioms_wholespace_identity.lean`：16 个公开声明全部
`[propext, Classical.choice, Quot.sound]`。

## 3. 缺口是什么

无残留缺口：`wholeSpace_identity` 完整证完（0 sorry/axiom，标准 3 公理）。
唯一的工程记号：`IReal_eq_cFrac_mul_homogeneousFourierENorm_sq` 用
`set_option maxHeartbeats 400000 in`（大 `ℝ≥0∞` calc，已注释）。
`lintegral_kernel_smul` 对所有 `s` 成立（两边可为 `⊤`），主定理只在 `0<s<1` 用有限性。
本车道不含 `torus_identity` / `localization`（其他车道）。
坑与失败路径见 `research/T13/ATTEMPTS_WHOLESPACE_IDENTITY.md`。

## 4. 跑了什么命令、什么结果

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.WholeSpaceIdentity
  → Build completed successfully (9358 jobs)；本模块 0 error 0 warning
cd verification && lake env lean ../formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean
  → 无输出（0 error 0 warning）
cd verification && lake env lean ../research/T13/probes/wholespace_identity_closes.lean
  → 无输出（0 error 0 warning）
cd verification && lake env lean ../research/T13/axioms_wholespace_identity.lean
  → 16 行，全部 [propext, Classical.choice, Quot.sound]
make check（worktree 根目录）
  → OK（architecture checks + contract policy 13 tests + work queue consistent）
```

辅助引理 `lintegral_kernel_smul` 由并行 prover 子代理独立证出（旋转+膨胀），
经本人独立复验（编译 0 输出、公理干净、签名逐字一致）后内联进模块。
