# REPORT — lane 335, T11 unit U12a: the periodic `H^m` energy identity

## 1. 证了哪个定理（which theorem is proved）

`paper/sections/appendix-a-local-theory.tex:127-141` 的高阶能量恒等式，在环面上、对
**真正的** `ClassicalSolutionT ν a f T`（不是 mild 解、不需要任何正则性谓词）：

对每个 `m : ℕ` 和每个内部时刻 `t ∈ Ioo 0 T`，

```
d/dt ‖u(t)‖²_{H^m} = −2ν‖∇u(t)‖²_{H^m} − 2⟪(u·∇)u(t), u(t)⟫_{H^m} + 2⟪f(t), u(t)⟫_{H^m}
```

其中压力项在**每一个频率上**就已经被无散度性消掉（论文 `:141` "the pressure term
vanishes by solenoidality"），`‖∇u‖_{H^m}` 用本模块的 `torusGradientNormAt` 拼写，
`⟪·,·⟫_{H^m}` 用 322 的 `torusRealPairing`。

这条恰好是 322 记录的 **missing fact A**（`ATTEMPTS_HIGH_ORDER.md` §3.1）。它**不**走
Section 4 的 `ℓ²` 数据路径路线（那条在本分支上被 `PeriodicQuantitativeLocalInput'` 堵住），
而是逐个标量 Fourier 系数求导再重新求和；`ClassicalSolutionT.sobolev` 只提供 `ContinuousOn G`，
而"高两阶的连续数据路径"正好就是逐项求导所需的控制。因此本条结果**没有任何命名输入**。

第二条结论：`hRhigh_of_pairingBound` 把 U12b 的配对估计作为**显式定理参数**（不是
`def … : Prop`）接进来，产出 322 的 `hRhigh` 原文（存在量词 `g` 取
`torusGradientNormAt m u t`）；`higherOrderBound_of_pairingBound` 与 322 的 Grönwall 链复合，
于是 `PeriodicContinuationAPI.higherOrderBound` 现在**只欠 missing fact B 一条**。

## 2. Lean 里现在有什么（what is in Lean now）

新模块 `formalization/NSFormalization/Section3/T11/EnergyIdentity.lean`，51 个声明，
全部只依赖 `[propext, Classical.choice, Quot.sound]`。主链：

| 声明 | 内容 |
|---|---|
| `velocityCoeffT` / `velocityDerivCoeffT` | `û ᵢ(t,k)` 与 `(∂ₜuᵢ)^(t,k)` |
| `hasDerivAt_velocityCoeffT` | **积分号下求导**：开时间域上 `d/dt û ᵢ(t,k) = (∂ₜuᵢ)^(t,k)`，只用 `velocity_smooth`（经 `Paper1.periodicFourierCoeff_eq_cube` + `PeriodicIntegration.hasDerivAt_cubeIntegral_of_contDiffOn`） |
| `velocityDerivCoeffT_momentum` | 动量方程的系数形式（压力显式，辅助引理）`d/dt û ᵢ(k) = −ν|2πk|²û ᵢ(k) + (f̂ ᵢ(k) − Q̂ ᵢ(k)) − 2πikᵢp̂(k)`，`Q = (u·∇)u = convectionFieldT u` |
| `velocityDerivCoeffT_momentum_projected` | **任务书要求的投影形式** `d/dt û(t)(k) = −ν·4π²|k|²·û(t)(k) + (P̂(f̂(t) − Q̂(t)))(k)`；`P̂` = `T10.periodicLeray` 在频率 `k` 上的符号（`lerayAt`，`rfl` 桥 `MildMomentum.periodicLeray_eq_lerayAt`，探针中给出） |
| `solenoidal_velocityDerivCoeffT` | `d/dt û` 也是无散度的（系数散度在 `Ioo 0 T` 上恒为 0，求导得 0） |
| `lerayAt_of_solenoidal` / `lerayAt_gradient` | `P̂` 固定无散度向量（`T10.Leray.periodicLeray_of_solenoidal` 的裸系数版）、湮灭梯度 `2πikᵢq` |
| `solenoidal_velocityCoeffT` | 由 `w.divergence` 得系数侧无散度 `∑ⱼ 2πikⱼû ⱼ(k) = 0` |
| `torusPressureSymbol_drop_raw` | 压力项逐频率归零（322 的 `torusPressureSymbol_drop` 的去权重版） |
| `hasSum_freqEnergyT` | 向量 Parseval：`‖u(t)‖²_{H^m} = ∑ₖ W(k)^m ∑ᵢ|û ᵢ(t,k)|²` |
| `exists_velocityDerivCoeffT_bound` | 紧时间窗上 `|(∂ₜuᵢ)^(r,k)| ≤ D`（单个 sup 界，与 `k` 无关） |
| `abs_freqEnergyDerivT_le` | 控制项 `|φ'ₖ(r)| ≤ 6MD·W(k)⁻²`，`M` 来自 `2m+4` 阶连续数据路径 |
| `hasDerivAt_torusSobolevNormAt_sq` | 逐项求导（`hasDerivAt_tsum_of_isPreconnected`），得 `HasDerivAt (fun r ↦ torusSobolevNormAt m u r ^ 2) (∑' k, freqEnergyDerivT m u k t) t` |
| `freqEnergyDerivT_split` | 单频率恒等式：耗散 + 力配对 − 对流配对（压力已消失） |
| `energyIdentity_of_classical` | **能量恒等式**，即上面第 1 节的式子 |
| `hRhigh_of_pairingBound` | 由 U12b 配对估计给出 322 的 `hRhigh` 原文 |
| `higherOrderBound_of_pairingBound` | 与 322 复合，给出 `higherOrderBound` 目标字段原文 |

辅助层同时给出：`periodicFourierCoeff_finsetSum`、`periodicFourierCoeff_sub_real`、
`periodicFourierCoeff_pressureGradient`（`∇p` 的系数 = `2πikᵢ p̂`）、
`advection_spatial_contDiff/_periodic`、`classical_velocity_slice_contDiff`、
`hasSum_datum_pair`（`⟪A,B⟫_{H^s}` 是其频率项之和）、`hasSum_gradEnergy`（耗散级数收敛，
被 `s+1` 阶能量控制）。

探针 `research/T11/probes/energy_identity_closes.lean`：
`hRhigh_closes`（322 binder 原文）与 `higherOrderBound_closes`
（`api_on_canonical.lean:111-120` 字段原文）都从单条配对假设闭合；
`projected_momentum_closes` 把任务书的投影系数方程（`4π²|k|²` 写开）原样闭合，
并用一条 `example` 给出 `periodicLeray s A i k = lerayAt k (fun j ↦ A.1 j k) i` 的 `rfl` 桥；
非平凡性用
空间齐次受力解 `u(t,x) = eᵗc`（`torusHomogeneousSolution`，`c ≠ 0`）：`HasDerivAt.unique`
把恒等式右端**钉死**在 `2e^{2t}‖K‖² > 0`，即在非零解、非零力上这条恒等式给出的是一个
严格正的具体数，不是空话。

审计 `research/T11/axioms_energy_identity.lean`：55 条 `#guard_msgs` 卡住的
`#print axioms`，每条都恰好是三条标准公理。

负例（reviewer 的符号突变，保留原文）`research/T11/probes/rev335_mutation_sign.lean`：
只把 `energyIdentity_of_classical` 结论里的耗散号 `-2*ν*…` 改成 `2*ν*…`，必须失败，
且失败在结论而不是漏前提：
```
error: Type mismatch
  energyIdentity_of_classical w hf m ht hGm hFm hNm
has type   HasDerivAt … (-2 * ν * torusGradientNormAt (↑m) w.velocity t ^ 2 + …) t
but is expected to have type
           HasDerivAt … ( 2 * ν * torusGradientNormAt (↑m) w.velocity t ^ 2 + …) t
```
该文件是**预期失败**的检查件（与 `rev330_negative.lean` 同惯例），不进门禁清单；
正面对照是探针里的 `energyIdentity_positive`（把右端钉死在 `2e^{2t}‖K‖² > 0`）。

## 3. 缺口是什么（what is missing）

只剩 322 的 **missing fact B**（U12b），本 lane 把它写成 `hRhigh_of_pairingBound` /
`higherOrderBound_of_pairingBound` 的**显式参数**（不是命名输入、不是 `def … : Prop`）：

```lean
∀ (ν : ℝ), 0 < ν → ∀ a ∈ initialClassT, ∀ f ∈ forceClassT,
  ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ Gm Nm : PeriodicSobolev (m : ℝ),
      IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm →
      IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm →
      |torusRealPairing Gm Nm| ≤
        Chigh m * torusSobolevNormAt 2 w.velocity t *
          torusSobolevNormAt (m : ℝ) w.velocity t *
          torusGradientNormAt (m : ℝ) w.velocity t
```

即 `|⟪(u·∇)u, u⟫_{H^m}| ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}`。它对非零解可满足（两边都是
有限实数，数据由 `T10.datum_unique` 唯一），不是目标的换名（目标是 `[0,S)` 上的一致界，
这条是逐时刻的乘积估计）。建议的起点仍是 lane 328 的实阶投影对流 CLM
`H^r × H^r → H^{r-1}`，外加 T12 的 `tameProduct`。

另外两处口径说明，供 lead 判断：

* 全树 gap search 只找到全空间的近亲，**没有**环面上用 `torusRealPairing` /
  `torusGradientNormAt` 拼写的那一条：`Section4/A03/OuterTameProduct.lean:172-179`
  `outerProductTame`（`ℝ³` 外积 tame 估计，是 SL5 的配料不是配对界）、
  `Section4/A04/HighEnergy.lean:125-146` `inner_energy_Rhigh`（全空间载体上的通用
  `eq:Rhigh` 内积步）、`Section4/A01/ConvectionDivergence.lean:111-118`（`ℝ³` 的
  advection/张量散度桥）。残留缺口是真的。
* 恒等式里的对流项用 `advection`（= `(u·∇)u`，动量方程残差里的那一项），不是
  `convectionDivergenceT`（张量散度）。在无散度下两者相等，但本 lane 不需要那条等式，
  所以没有引入。若 U12b 更方便在张量散度形式上做，桥接引理（`advection = ∇·(u⊗u)`，
  用 `w.divergence`）应放在 U12b 一侧。
* `‖∇u‖_{H^m}` 没有现成拼写（T10 的 `periodicHomogeneousENorm` 只对零均值场定义），
  本模块定义 `torusGradientNormAt s u t := √(∑ₖ W(k)^s|2πk|²∑ᵢ|û ᵢ|²)`，这正是
  `(∑ⱼ‖∂ⱼu‖²_{H^s})^{1/2}`；322 的存在量词 `g` 就取它。

## 4. 跑了什么命令、什么结果（commands and results）

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.EnergyIdentity
  → ✔ [9993/9993] Built NSFormalization.Section3.T11.EnergyIdentity, Build completed successfully
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/EnergyIdentity.lean
  → 无输出（0 error、0 warning）
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/energy_identity_closes.lean
  → 无输出
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_energy_identity.lean
  → 无输出（55 条 #guard_msgs 全部通过）
make check   → RC=0
make test    → RC=0（已注册合同闭包不受影响）
```

无 `sorry` / `admit` / `axiom` / `native_decide`，无 `set_option maxHeartbeats`，
未修改任何既有文件的数学内容。

**精确 diff**（`git diff --name-status origin/erenup/integration-section3...HEAD`，
合并基取 `2c483236`；注意本车道基线里已本地并入 322 与 327，所以它们的文件在这里
也显示为新增 `A`，不是本车道的改动）：

```
A  formalization/NSFormalization/Section3/T11/EnergyIdentity.lean      ← 本车道
A  formalization/NSFormalization/Section3/T11/HighOrder.lean           ← lane 322（已并入基线）
A  formalization/NSFormalization/Section3/T11/MildMomentum.lean        ← lane 327（已并入基线）
A  research/T11/ATTEMPTS_ENERGY_IDENTITY.md                            ← 本车道
A  research/T11/ATTEMPTS_HIGH_ORDER.md                                 ← lane 322
A  research/T11/ATTEMPTS_MILD_MOMENTUM.md                              ← lane 327
M  research/T11/EXISTENCE_ROUTE.md                                     ← lane 327
A  research/T11/REPORT_322.md / REPORT_327.md                          ← 322 / 327
A  research/T11/REPORT_335.md                                          ← 本车道
M  research/T11/T11_SPLIT.md                                           ← 本车道只追加一行（322/327 各自的行已在基线里）
A  research/T11/axioms_energy_identity.lean                            ← 本车道
A  research/T11/axioms_high_order.lean / axioms_mild_momentum.lean     ← 322 / 327
A  research/T11/probes/energy_identity_closes.lean                     ← 本车道
A  research/T11/probes/high_order_closes.lean / mild_momentum_closes.lean ← 322 / 327
```

复审后另加：`research/T11/probes/rev335_mutation_sign.lean`（reviewer 的负例，原样保留）
与 `research/T11/REVIEW_335-T11-U12a-energy-identity.md`。本车道**没有**修改
`HighOrder.lean` / `MildMomentum.lean` 或任何既有模块。
