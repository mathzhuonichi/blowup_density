# 审稿 · lane 094 (D01 · P2 · SL7b-α) — order-0 transverse Fourier identity

审稿人跑通 Lean。被审文件：`formalization/NSFormalization/Section4/D01/OrderZeroSymbol.lean`（520 行，31 个声明），
`research/D01/ATTEMPTS_ORDER_ZERO.md`，`research/D01/axioms_order_zero.lean`。

## 结论

**ACCEPT-WITH-NOTES**

数学正确，陈述与 079 的 transverse 形状逐 token 一致，**主定理的假设确实只有 `MemLp z 2 volume` + `ContDiff ℝ ∞ z` +
逐点 `div z = 0`，没有任何关于导数的可积性**——这正是 SL7b 要的非循环种子。所有 findings 都是卫生问题
（重复 + ATTEMPTS 记录不准），没有正确性缺陷，不阻塞合入。

---

## 1. 编译 / 公理 / 门禁

| 命令 | 结果 |
|---|---|
| `lake build NSFormalization.Section4.D01.OrderZeroSymbol` | `Build completed successfully (9882 jobs).` |
| `lake env lean ../formalization/NSFormalization/Section4/D01/OrderZeroSymbol.lean` | **无任何输出**（无 warning、无 sorry），exit 0 |
| `lake env lean ../research/D01/axioms_order_zero.lean` | 20 条，**每条恰好 `[propext, Classical.choice, Quot.sound]`** |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option'` | 唯一命中是第 36 行 docstring 里的散文 "No `sorry`, no `axiom`"；**无实际出现** |
| `make check` | exit 0（`test_contract_policy` 13 tests OK；`check_work_queue` 30 items consistent） |

审计脚本的 20 条覆盖了全部承重定理。未列入的 11 个（`bump`、`bump_smooth/cs/le1/nonneg/one`、`chi`、
`chi_le1`、`chi_nonneg`、`Pj`、`zc`）是 4 个 `def` + 7 个一行 Mathlib 包装，被 `Cut.physical_pairing_zero`
的审计**传递覆盖**，无风险。仅备案。

---

## 2. 陈述保真（核心）

### (a) 假设里没有夹带导数可积性 —— **确认**

`#check @orderZeroDatum_transverse_of_divergence_free` 打出的完整签名（`pp.numericTypes`）：

```
∀ {z : Space → Space} (hz : MemLp z 2 volume),
  ContDiff ℝ (↑⊤) z →
    (∀ (x : Space), ∑ j, (partialDeriv j z x).ofLp j = (0:ℝ)) →
      ∀ᵐ (ξ : Space), ∑ j, ↑(ξ.ofLp j) * ↑↑↑((orderZeroDatum hz).ofLp j) ξ = (0:ℂ)
```

三个假设，一个不多。整条链（`cs_pairing_zero` → `physical_pairing_zero` → `tempered_div_zero` →
`fourier_transverse` → `orderZeroDatum_transverse_symm` → Lemma A）逐个 `#check` 过，
**没有任何一条**出现 `SmoothL2Field`、`MemLp (fderiv …)`、`Integrable (partialDeriv …)`、`HasCompactSupport z`。
`grep -nE "SmoothL2Field|MemLp \(fderiv|Integrable \(partialDeriv|HasCompactSupport z"` 在整个模块里只命中
第 12 行的 docstring。

关于 `z` 的导数，链上只用到两件事：**连续性**（`hzdcont`，由 `ContDiff` 给）和「compact support 的 φ 乘上去后可积」
（`(hφcont.smul hzdcont).integrable_of_hasCompactSupport hφc.smul_right`）。后者正是 Schwartz 路线做不到、
cutoff 路线做得到的那一步。

### (b) 结论与 079 形状一致，且一行喂进 consumer —— **确认**

079 `Transverse.lean:226` 的结论是 `∀ᵐ ξ, ∑ j, ((ξ j : ℝ) : ℂ) * ((A j : FourierData) ξ) = 0`；
094 是同一串 token，只把 `A` 换成 `orderZeroDatum hz`。在 `/tmp/rev094/consumer.lean` 里验证（编译通过）：

```lean
theorem consumer_one_line (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0) :
    Leray.lerayComplement 0 (orderZeroDatum hz) = 0 :=
  Leray.lerayComplement_eq_zero_of_transverse 0 (orderZeroDatum hz)
    (orderZeroDatum_transverse_of_divergence_free hz hsmooth hdiv)
```

term mode 一行，无 `by`，无 defeq 打磨。`LerayDatum.lean:316` 的 consumer 接得上。

### (c) 分析核心 `Cut.physical_pairing_zero`（:198）—— 正确

读法确认，cutoff 论证是这样走的（`χ_R(x) = χ((n+1)⁻¹x)`，`R = n+1`，`χ = ContDiffBump ⟨1,2⟩`）：

* **C_c^∞ 一步**（`cs_pairing_zero` :156）：`φ = χ_R ψ` 紧支，Mathlib
  `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` 的**三条**可积假设全部由紧支打掉——关键是第二条
  `Integrable (fun x ↦ f x • fderiv ℝ g x v)`，即 `φ · ∂ⱼz` 可积。对 Schwartz `ψ` 这条不成立，对紧支 `φ` 成立。
  求和后用 `hdiv` 把导数侧整体消掉。
* **Leibniz 分裂**（`hterm`）：`∂ⱼ(χ_R ψ) = χ_R ∂ⱼψ + ψ ∂ⱼχ_R`，两部分分别可积（都由紧支给），所以
  `integral_add` 合法。
* **B 项 → 目标（DCT）**：控制函数是 `fun x => ‖(∂_{eⱼ}ψ) x • zc z j x‖`，可积性来自
  `hMdψ j : Integrable ((∂_{eⱼ}ψ) • zc z j)`，而这条由 **Schwartz × L²（Hölder，两边都在 L²，积在 L¹）**给出
  ——用的是 **ψ 的导数**在 L²，不是 z 的。逐点界 `‖χ_R‖ ≤ 1`（`hchic_le1`），逐点收敛
  `χ_R(x) → 1`（`chi_eventually_one`：`n ≥ ⌈‖x‖⌉` 时 `‖(n+1)⁻¹x‖ ≤ 1`，落在 `rIn = 1` 的平台上）。✓
* **A 项 → 0（边界项）**：`‖∇χ_R‖ ≤ C/R` 在本树的表述里是
  `Cut.chi_deriv_bound : ‖fderiv ℝ (chi n) x (coordinateVector j)‖ ≤ C * ((n:ℝ)+1)⁻¹`，
  由链式法则 `fderiv(χ∘(R⁻¹·)) = fderiv χ(R⁻¹x) ∘ (R⁻¹ • id)` 得出，`C` 的存在性由
  `exists_deriv_bound`（`fderiv bump` 连续 + 紧支 ⇒ 取到最大值）给出。**scaling 正确**。
  乘上去的那个积分是 `∫ ‖ψ • zⱼ‖`，与 `n` 无关且有限（`hMψ j`，同样是 Schwartz × L² ⊂ L¹），
  于是 `squeeze_zero_norm` 给 A → 0。✓
* **收尾**：`hcancel n : (∑B) + (∑A) = 0` ⇒ `∑B → 0`；与 `hBlim` 的极限比较（`tendsto_nhds_unique`）。✓

粗糙但正确：`‖∇χ_R‖ ≤ C/R` 是**全局**用的，没有限制到环 `R ≤ |x| ≤ 2R`——只损失一个常数，不影响结论。

### (d) 基本引理的副条件 —— 诚实

用的是 `MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero`
（`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:186`）：

```
theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf : LocallyIntegrable f μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0
```

副条件 `LocallyIntegrable (∑ⱼ ξⱼ · 𝓕zⱼ)` 由 `hlocterm` 老实给出：`𝓕(componentLp hz j) ∈ L²`
⇒ `MemLp.locallyIntegrable (1 ≤ 2)`，再乘上连续的 `ξ ↦ ξⱼ`（`LocallyIntegrableOn.continuousOn_mul`），
最后 `locallyIntegrable_finsetSum`。测试函数侧把实值 `g` 经 `Complex.ofRealCLM` 提成
`HasCompactSupport.toSchwartzMap`，再喂 `hpair`。**没有偷换**。

### (e) `2πi ξ` 的符号/归一化 —— 无关，确实抵消

`TemperedDistribution.fourier_lineDerivOp_eq` 给出的常数在 `hterm` 里被整体提出
（`Finset.mul_sum`），随后 `(mul_eq_zero.mp happ).resolve_left hπ`，`hπ : 2π i ≠ 0`。
结论是「= 0」，任何非零常数都抵消，**符号与 2π 约定不影响结论**。✓
dilation 的搬运方式与 079 完全一致（见 F1）。

### (f) 非空洞性 —— 确认（两条，都编译通过）

1. 假设有 inhabitant：`MemLp.zero`、`contDiff_const` 给零场；`div = 0` 平凡。
   （更有意义的紧支无散度场存在但构造耗时，此处不必要：下面第 2 条已排除空洞。）
2. **datum 不是零**：验证了
   `orderZeroDatum hz j = 0 → componentLp hz j = 0`（经 `orderZeroDatum_coe` + `cyclesToAngular` 是
   `LinearIsometryEquiv` + `fourierInv_fourier_eq`）。所以 `orderZeroDatum` 忠实地携带 `z`，
   结论 `∑ ξⱼ Âⱼ = 0` 是对 `𝓕z` 的真实约束（a.e. `𝓕z(ξ) ⊥ ξ`），不是因为 datum 恒零而平凡成立。
   `isSobolevDatum_orderZeroDatum`（`OrderZeroDatum.lean:104`）同向佐证。

---

## 3. Findings

### F1 · 中 · `OrderZeroSymbol.lean:483–520` · dilation 搬运是 079 的逐字复制

`orderZeroDatum_transverse_of_divergence_free` 的证明体与
`Transverse.lean:226–265`（`transverse_of_divergence_free`）在把 `A j` 换成 `orderZeroDatum hz j` 之后
**38 行里只有 6 行实质不同**（签名、`hstar` 的来源、一处换行、`have h := ht`）。
`Longitudinal.lean:174–233` 是同一段 κ / `hMP` / `hfwd` 样板的**第三份**。
ATTEMPTS 的 "Reused (not re-proved): `Transverse.angularFrequencyDilation_coeFn`" 只对了一半——
被复用的是 coeFn 引理，**搬运本身是重证的**。

已在 `/tmp/rev094/factor.lean` 验证（编译通过）：把证明体原样搬到一个裸族上

```lean
theorem transverse_of_transverse_symm {g : Fin 3 → FourierData}
    (hstar : ∀ᵐ ξ, ∑ j, ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (g j)) ξ = 0) :
    ∀ᵐ ξ, ∑ j, ((ξ j : ℝ) : ℂ) * ((g j) ξ) = 0
```

之后 **079 的 SL4 deliverable 和 094 的 Lemma A 各自一行**：

```lean
example … := transverse_of_transverse_symm (transverse_symm_of_divergence_free hdiv m hA)
example … := transverse_of_transverse_symm (orderZeroDatum_transverse_symm hz hsmooth hdiv)
```

**修法**：把这条提为独立引理（放 `Transverse.lean`，或随 `angularFrequencyDilation_coeFn` 一起进
`Paper3/AngularFourierDilation.lean` —— `Transverse.lean:60–64` 的 docstring 已经计划了这次搬迁），
两处各减约 30 行；Lemma B 落地时 `Longitudinal.lean` 再减一份。可以合入后由 SIMP lane 做。

### F2 · 中 · `ATTEMPTS_ORDER_ZERO.md`「Tactic traps」· 四条里三条复现不出来

按硬规矩 4（正负例都要记），负例记错比不记更贵。逐条实测：

| 记录的坑 | 实测 |
|---|---|
| `HasFDerivAt.const_smul` 触发 bogus `ContinuousSMul ℚ≥0` instance search | **诊断不对**。在 `chi_deriv_bound` 的原位替换后确实失败，但报的是 metavariable/defeq 不匹配：`HasFDerivAt (?c • id) (?c • ContinuousLinearMap.id ?R Space)` 对不上 `fun y => (↑n+1)⁻¹ • y`，标量环是 metavariable。**显式给出标量就能过**（`(hasFDerivAt_id x).const_smul (((n:ℝ)+1)⁻¹)` 编译通过）。与 `ContinuousSMul ℚ≥0` 无关 |
| `fderiv_mul` 同样触发该 instance 陷阱，故用 `show … from (hc_fd.mul hd_fd).fderiv` 桥 | **复现不出**。`fderiv_mul hf.differentiableAt hg.differentiableAt` 直接给出 `f x • fderiv g x + g x • fderiv f x`，编译通过，比现用的 `show … from` 桥更短 |
| 用 `Continuous.tendsto ∘ tendsto_inv_atTop_zero` 代替 `Tendsto.const_mul`（同一 instance 陷阱） | **复现不出**。`(hcn0.const_mul C).mul_const M` + `simpa` 3 行编译通过，现用的 `hcont.tendsto 0` 绕路 6 行 |
| `integral_finsetSum` 需要显式 summand `(f := …)` | **复现不出**。term 位置和 `rw … at h` 位置各测一次，不给 `(f := …)` 都过 |

**修法**：按实测重写这四行。第 1 条改成「`const_smul` 的标量环会留成 metavariable，必须显式给标量，或直接用
`(c • ContinuousLinearMap.id ℝ E).hasFDerivAt`」；第 2、3、4 条删掉（或标注「未复现」）。
顺带可以按 F2 表里更短的写法简化 `chi_deriv_bound`、`hterm`、`hAlim` 的收尾——属 SIMP lane 范畴。

### F3 · 低 · `ATTEMPTS_ORDER_ZERO.md`「Negative examples」第 1 条 · 反例结论说过头了

原文：`z_j = a·cos∘ψ`，`a ~ |x|^{-d/2-ε} ∈ L²`，`|∇ψ| ~ e^{|x|}`，「which **no** Schwartz `φ` can render integrable」。

**这句是错的**：Gauss 型 `φ = e^{-|x|²}` 衰减远快于 `e^{|x|}` 增长，`φ ∂z` 可积。

需要的、也成立的是**弱得多**的版本：*存在* Schwartz `φ` 使其不可积。取
`φ(x) ≈ e^{-|x|^{1/2}}`（光滑化后是 Schwartz：它和它的各阶导数都快于任何多项式衰减，但慢于任何指数），
配 `|∂₁z_j| ~ |x|^{-3/2-ε} e^{x₁}`，则 `φ|∂z| ~ |x|^{-3/2-ε} e^{x₁ - |x|^{1/2}} → ∞`，不可积。
这就足够堵死 `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` 的第二条假设
`Integrable (ψ • ∂ⱼz)`——该引理要求对**给定的** ψ 成立，所以有一个反例即可。

**修法**：把结论改成「并非每个 Schwartz `φ` 都能把它变可积，故 `Integrable (ψ • ∂ⱼz)` 一般无法 discharge」，
并把见证函数从 Gauss 改为 `e^{-|x|^{1/2}}` 型。**论证方向本身是对的，cutoff 确实必要**（见下条）。

另外两条负例**核实为真**：

* **Mathlib 确实没有** "C_c^∞ dense in Schwartz"，也没有 "在 C_c^∞ 上消失的 tempered distribution 为零"。
  全 Mathlib 搜 `Dense` ∩ `Schwartz` 只有一条 `SchwartzMap.toLpCLM` 的 `DenseRange`
  （`SchwartzSpace/Basic.lean:1384`，方向是 Schwartz → Lp，用不上）。
  这条**很关键**：Fourier 那步必须在 `𝓢'` 里做，即必须对**所有** Schwartz `ψ` 有配对恒等式，
  所以 cutoff/`R→∞` 是**必需**而非便利。核实无误。
* **HeliCorgi 的散度桥确实反向**。`R3ClassicalIncompressibility.lean:212`
  `r3PhysicalRepresentative_incompressible_of_mem_solenoidal` 与
  `:109 r3RawDivergence_ae_zero_of_mem_solenoidal` 都是 *Fourier solenoidal ⇒ 物理无散度*；
  物理 ⇒ Fourier 只有 Schwartz 级的 iff（`R3SchwartzDivergence.lean:130`
  `r3Schwartz_rawDivergence_fourier_iff_classical`，对象是 `R3SchwartzVelocity`，不是仅 `MemLp` 的光滑 `z`）。
  核实无误，HeliCorgi 供不出 Lemma A。

### F4 · 低 · `OrderZeroSymbol.lean:129, 198` · `Cut.zc` 泄漏进公开陈述

`physical_pairing_zero` 的结论写成 `∑ⱼ ∫ (∂_{eⱼ}ψ) x • zc z j x = 0`。`zc` 是本模块的 `def`，
下游只能靠 defeq 展开（`tempered_div_zero` 里就是 `rw [hx]; rfl`）。
**修法**（可选）：陈述里直接写 `fun x => ((z x j : ℝ) : ℂ)`，或补一条 `zc_apply` 的 `@[simp]`。不阻塞。

### F5 · 低（信息） · 导入耦合

`OrderZeroSymbol.lean` 为了一条 `angularFrequencyDilation_coeFn` 而 import `Transverse.lean`，
从而拖入 `DerivativeDatum` / `SmoothL2Field`——正是 SL7b 存在的理由所要绕开的那个 wrapper。
**陈述不受影响**（已逐条核实假设里没有它），但 F1 的提升（连同 `Transverse.lean:60–64` 已规划的
`Paper3/AngularFourierDilation.lean` 搬迁）会顺手解耦。`LerayLowering.lean:104` 也在用同一条，
共 4 处使用、3 份搬运样板。

---

## 4. 一致性（check 3 小结）

* 导入规范：`Contracts/*` 未被触碰；本模块在 `formalization/` 下，import 的是 canonical 的
  `A03.OuterTameProduct (partialDeriv)`、`D01.OrderZeroDatum`、`D01.Transverse` 加 Mathlib。`make check` 通过。
* **无重述定义**：`Cut` 里的 `bump` / `chi` / `Pj` / `zc` 都是本模块新引入的辅助对象，不是对上游定义的重述，
  没有触发 `rfl` 桥的要求。
* **重复**：见 F1（dilation 搬运）。此外 `Cut.cs_pairing_zero` 内联的 `hibp`（单项 IBP）本身是 index-generic
  的，被写死成 `k = j`，见下节。

---

## 5. Lemma B（order-0 curl-free / longitudinal）：该抽什么、该抄什么

**有一条统一的「反对称配对」引理，抽出来之后 Lemma B 的物理层只要 ~10 行，不是 ~100 行。** 已实测。

关键观察：`cs_pairing_zero` 里内联的 `hibp` 对两个指标是通用的，只是被写死成 `k = j`。把它解耦成

```lean
theorem cs_ibp (hsmooth : ContDiff ℝ ∞ z) {φ} (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (j k : Fin 3) :
    (∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector k))
      = -∫ x, (fderiv ℝ φ x (coordinateVector k)) • zc z j x
```

（连同 `fderiv_zc_eq` 的两指标版 `fderiv_zc_eq' : fderiv ℝ (zc z j) x (coordinateVector k) = ↑(partialDeriv k z x j)`，
现版 :142 也只写了 `k = j`），散度情形和旋度情形就都是它的实例。
在 `/tmp/rev094/lemB.lean` 里跑通了（编译无输出）：

```lean
theorem cs_antisym_pairing_zero (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i)
    {φ} (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (p q : Fin 3) :
    (∫ x, (fderiv ℝ φ x (coordinateVector p)) • zc z q x)
      - (∫ x, (fderiv ℝ φ x (coordinateVector q)) • zc z p x) = 0
```

证明体 **7 行**（`cs_ibp` 两次 + `hcurl` 的逐点相等 + `linear_combination`）。
`cs_ibp` + `fderiv_zc_eq'` + `cs_antisym_pairing_zero` 合计 45 行，其中 `cs_ibp` 是从 094 现有代码里搬出来的。

**真正该做的因式分解**：把 `physical_pairing_zero`（~130 行 cutoff 机器）改写成**常数权重矩阵**的形式

```lean
theorem physical_weighted_pairing_zero (hz) (hsmooth) (w : Fin 3 → Fin 3 → ℂ)
    (hw : ∀ x, ∑ j, ∑ k, w j k * ((partialDeriv k z x j : ℝ) : ℂ) = 0) (ψ : SchwartzMap Space ℂ) :
    ∑ j, ∑ k, w j k * ∫ x, (∂_{coordinateVector k} ψ) x • zc z j x = 0
```

—— 散度是 `w = δ`，旋度对 `(p,q)` 是 `w q p = 1, w p q = -1`。cutoff/DCT/`C/R` 那套机器**与指标无关**
（逐 `j` 走 DCT 再求和，权重只是常数），所以这是机械推广，行数基本不变，但**只写一次**。

结论：
* **必须重复的**：几乎没有。
* **应当抽出的**：`cs_ibp`（两指标 IBP，已在 094 内部内联）、`fderiv_zc_eq'`（两指标）、
  `physical_pairing_zero` 的权重矩阵版、`fourier_transverse` 里内联的 `hterm`
  （单分量的 `𝓕(∂_k T_{z_j})ψ = 2πi ∫ ξ_k ψ 𝓕z_j`，抽出来后 Lemma B 的 Fourier 步直接复用）、
  以及 F1 的 dilation 搬运。
* **抽完之后 Lemma B ≈ 30–40 行**：`cs_antisym_pairing_zero`（7 行）+ 权重实例（~5 行）+
  `tempered_curl_zero` / `fourier_longitudinal`（~15 行，`ae_all_iff` 把 9 个 pair 合起来）+
  datum/dilation（~5 行，若 F1 提升后另需一条 longitudinal 版搬运，同样可从 `Longitudinal.lean:174` 抽）。
* **不抽的话 Lemma B ≈ 150 行**，且是 `physical_pairing_zero` 的第二份 cutoff 拷贝。
  **建议：把这次因式分解作为 Lemma B 那条 lane 的第一步，而不是事后 SIMP。**

## 6. SL7b 剩下的步骤（走向 `(I−P) datum⁰(h) = datum⁰(∇p)`）

094 交付的是 `eq:Rpressure` 分解的 **transverse 一半**。按 `P2_SPLIT.md` SL7(7b)，目标是
`h = ∂ₜu + ∇p`（`h = f − ∇·(u⊗u)`）在 order 0 的 `lerayComplementVectorL 0 (A⁰_h) = A⁰_{∇p}`。还差：

1. **Lemma B**（order-0 longitudinal，上节）+ `Longitudinal.lean:255`
   `lerayComplement_eq_self_of_longitudinal`，给 `(I−P) datum⁰(∇p) = datum⁰(∇p)`。
   曲率自由性由 `∇p` 的 Clairaut 对称（`Mathlib` 二阶导对称）给出，`∇p` 光滑来自 `ClassicalSolutionR`。
2. **`orderZeroDatum` 的可加性**：`OrderZeroDatum.lean` 里**没有**
   `orderZeroDatum (h₁+h₂) = orderZeroDatum h₁ + orderZeroDatum h₂`。
   最省事的路线是走 datum 的唯一性（`angularRealization_injective` + `isSobolevDatum_orderZeroDatum`），约 15 行。
3. **`lerayComplement` 的线性**：`LerayDatum.lean:118` 已有 `lerayComplementAmbientLM`（LinearMap）
   和 `:152 lerayComplementAmbient`，所以 `lerayComplement_add` 应当是几行。
4. **`∂ₜu(t,·)` 的 `MemLp 2` 与 `ContDiff ∞`**（在 `MemForceR f` 下由 `A02/SolutionClass` 给），
   以及 `∇p(t,·)` 的 `MemLp 2`（`ClassicalSolutionR.pressure_gradient`）。这是 SL7b 剩下的主要 plumbing。
5. **`hdiv` 槽已经对上**：实测 074 的
   `DivergenceTime.spatialDivergence_temporalDerivative_eq_zero u ht x` **按 `rfl` 直接填进**
   094 的 `∀ x, ∑ j, partialDeriv j (fun y => temporalDerivative u.velocity t y) x j = 0`
   （`/tmp/rev094/sl7b.lean`，编译通过）。这一环无缝。

即：094 之后，SL7b 的关键路径是 **Lemma B → datum 可加性 + lerayComplement 线性 → `∂ₜu`/`∇p` 的 `MemLp`**，
其中只有 Lemma B 含新数学，其余是 assembly。

---

## 7. 跑过的命令与结果

```
bash scripts/lean-install.sh                                              → == OK
cd verification && lake build NSFormalization.Section4.D01.OrderZeroSymbol
                                                → Build completed successfully (9882 jobs).
cd verification && lake env lean ../formalization/.../OrderZeroSymbol.lean → 无输出, exit 0
cd verification && lake env lean ../research/D01/axioms_order_zero.lean
                                                → 20 条, 全部 [propext, Classical.choice, Quot.sound]
grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' OrderZeroSymbol.lean
                                                → 仅 :36 docstring 散文
make check                                                                → exit 0
lake env lean /tmp/rev094/consumer.lean   (consumer 一行 + 零场 inhabitant + datum 忠实性) → 通过
lake env lean /tmp/rev094/factor.lean     (共享 dilation 搬运引理, 079+094 各一行)        → 通过
lake env lean /tmp/rev094/sigs.lean       (全链签名, pp.numericTypes)                     → 见 §2(a)
lake env lean /tmp/rev094/pitfall.lean    (孤立位置复现两个坑)                            → 均不复现
lake env lean /tmp/rev094/pitfall2.lean   (原位复现三个坑)                    → 仅 const_smul 失败, 错因不同
lake env lean /tmp/rev094/pitfall3.lean   (integral_finsetSum 在 rw 位置无 hint)          → 通过, 不复现
lake env lean /tmp/rev094/lemB.lean       (两指标 IBP + 反对称配对原型, 45 行)            → 通过
lake env lean /tmp/rev094/sl7b.lean       (074 的 hdiv 按 rfl 喂进 094)                   → 通过
```

审稿人：opus reviewer（lane 094），2026-09-13。
