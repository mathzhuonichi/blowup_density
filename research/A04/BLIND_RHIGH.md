# BLIND_RHIGH — 盲稿比对：eq:Rhigh（lane 130-SPEC-A04-rhigh-blind）

Comparer 报告。对象：`paper/sections/appendix-a-local-theory.tex:132-137` 的 display
`eq:Rhigh`（段落 `:127-140`，`:129` "For every integer $m\ge3$"，`:139` "justified by
Fourier approximation on compact intervals of smooth existence"）。

三个被比对的陈述：

| 标签 | 出处 | 词汇 |
|---|---|---|
| **A** | `research/A04/blind/rhigh_A.lean` `BlindRhighA.eqRhigh_A`（lane 130 writer A） | 合同 `Contracts.V1.{Data,TameProduct}` + 自建实值包装 |
| **B** | `research/A04/blind/rhigh_B.lean` `BlowupDensity.Research.A04.RhighB.eqRhigh_B`（writer B，与 A 互不可见） | 同上 |
| **tree** | `formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean:145-155` `energyIdentityHigh`（lane 128；与 spec 字段 `research/A04/Spec.lean:424-434` 逐 token 相同，见 `REVIEW_ENERGY_HIGH.md` §2(a)） | formalization 词汇（`HasSmoothSobolevPath` / `sobolevNormAt` / `gradientSobolevNormAt` / `Chigh`） |

探针目录 `/tmp/rev130/`。环境 `. scripts/lean-env.sh`，`lake` 一律从 `verification/` 跑。

---

## 1. 两份盲稿都编译

```
$ . scripts/lean-env.sh && cd verification
$ lake build Contracts.V1.Data Contracts.V1.TameProduct
Build completed successfully (8817 jobs).

$ lake env lean ../research/A04/blind/rhigh_A.lean
BlindRhighA.eqRhigh_A : Prop
EXIT=0

$ lake env lean ../research/A04/blind/rhigh_B.lean
BlowupDensity.Research.A04.RhighB.eqRhigh_B : Prop
EXIT=0
```

两个文件除 `#check` 外静默；无 `sorry` / `axiom` / `native_decide`。

---

## 2. A vs B：**没有任何建模差异**——两个 `Prop` 是同一个 `Prop`

这是本 lane 最强的一条结论：两位互不可见的写手给出的不是"等价"陈述，而是**定义相等**的陈述。
`/tmp/rev130/p1_ab.lean` 把两份文件的 `def` 逐字抄进同一个文件（只去掉 docstring），证：

```lean
theorem AB_eq  : BlindRhighA.eqRhigh_A = BlowupDensity.Research.A04.RhighB.eqRhigh_B := rfl
theorem AB_iff : BlindRhighA.eqRhigh_A ↔ BlowupDensity.Research.A04.RhighB.eqRhigh_B := Iff.rfl
theorem norm_eq   : BlindRhighA.hmNorm     = …RhighB.hmNorm     := rfl
theorem normSq_eq : BlindRhighA.hmNormSq   = …RhighB.hmNormSq   := rfl
theorem grad_eq   : BlindRhighA.gradHmNorm = …RhighB.gradHmNorm := rfl
theorem h2_eq     : BlindRhighA.h2Norm     = …RhighB.h2Norm     := rfl
theorem f_eq      : BlindRhighA.hmNorm     = …RhighB.fHmNorm    := rfl
```
```
$ lake env lean /tmp/rev130/p1_ab.lean
'Rev130.AB_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

逐项对照（`paper` 列 = 论文支持哪一读法）：

| 建模点 | A | B | tree | paper | 结论 |
|---|---|---|---|---|---|
| 导数形式 | `DifferentiableAt ℝ (hmNormSq …) t →` 前件 + `deriv` | 同 A，逐字 | `∃ d, HasDerivAt (fun r => sobolevNormAt m u r ^2) d t ∧ …` | `:132` 写 `\frac{\dd}{\dd t}`，`:139` **断言**它成立（"These identities are justified by …"） | A=B；**tree 更忠实**（论文是断言可微，不是假设可微）。两位写手都在 md 里把 `∃ d, HasDerivAt` 记为 "rejected #1 / Rejected B，valid and slightly stronger"，即两人都看见了这条，只是任务措辞让他们选了前件形 |
| 时间集 | `t ∈ Ioo 0 T` | `t ∈ Set.Ioo 0 T` | `∀ t ∈ Ioo (0:ℝ) T` | 论文未明写；`momentum` 只在内点成立，双侧导数需内点 | 三者一致 |
| 范数取实 | `.toReal` of `ℝ≥0∞` | `.toReal` | `.toReal`（`sobolevNormAt`/`gradientSobolevNormAt` 的定义） | 不适用（论文在 ℝ 里） | 三者一致；`⊤ ↦ 0` 注意事项 A/B 都在 docstring 里写了 |
| `‖u‖_{H^m}` | `Data.sobolevENorm (m:ℝ) (fun x => u (t,x))` | 同（经 `slice`） | `D01.sobolevENorm …`（与合同 `rfl` 相等，`/tmp/rev128/p5_hssp_bridge.lean`） | `01-introduction.tex:81` 的固定时刻空间范数 | 三者一致 |
| `‖∇u‖_{H^m}` | `TameProduct.gradientSobolevENorm` | 同 | `A03.gradientSobolevENorm`（`rfl` 相等） | `:134` 字面写 `\norm{\nabla u}_{H^m}` | **三者一致**，都拒绝了 `‖u‖_{H^{m+1}}` 的阶移读法。这是 `REVIEW_ENERGY_HIGH.md:437` 点名的"第二读者唯一可能分歧处"之一，两位盲写手独立地都没分歧 |
| 耗散项 | `ν * (gradHmNorm)^2` | `ν * gradHmNormSq`（同一表达式） | `ν * gradientSobolevNormAt … ^ 2` | `+\nu\norm{\nabla u}_{H^m}^2` | 三者一致 |
| `‖f‖_{H^m}` | `hmNorm m f t`（f 的切片空间范数，未投影） | `fHmNorm m f t`（同一表达式） | `sobolevNormAt (m:ℝ) f t` | `:136`，逐点时间、未投影 `f` | 三者一致 |
| 常数量化 | `∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ …`，最外层 | 逐字同 A | 具名 `Chigh m`（`= A03.outerTameConst m`），另有 `Chigh_pos` | `C_m` 只依赖 `m`（与 `ν, a, f, T, w` 无关） | A=B；**tree 更强**（给出常数）。记录：合同 record 里写 `Chigh : ℕ → ℝ` + `Chigh_pos` 两个字段，**就是** A/B 的 `∃C` 的 Skolem 化，二者不冲突 |
| 阶范围 | `∀ m : ℕ, 3 ≤ m` | 同 | 同 | `:129` "For every integer $m\ge3$" | 三者一致（tree 的 128 审稿另记：`2 ≤ m` 其实够用，属 V2 加强，不改 V1） |
| 假设包 | `0 < ν`、`a ∈ initialClassR`、`MemForceR f`、`ClassicalSolutionR ν a f T` | 同 | 同 **＋ `HasSmoothSobolevPath T w.velocity`** | 论文 `:72-77` 断言 `C^j_tH^k_x` for all `j,k` | 见 §3/§4 |
| ∀ 前缀顺序 | `∀ ν, 0<ν → ∀ a, a∈… → ∀ f, MemForceR f → ∀ T w m …` | 同 | `∀ ν a f T, 0<ν → … → ∀ w …` | — | 纯排版差异，逻辑同值（§3 两个方向的证明都跨过了它） |

**A/B 一致 = 无歧义的证据**：`REVIEW_ENERGY_HIGH.md` 事先点名的两处可能分歧（`‖∇u‖_{H^m}` 的读法、
`Ioo` 双侧 vs `Ico` 单侧）两位写手都与 tree 同向选择。唯一"分歧"是 A/B 共同 vs tree 的导数打包形式，
而两位写手都在 md 里**显式记录**了 `∃ d, HasDerivAt` 这条备选并称它"valid and slightly stronger"。

---

## 3. A/B vs tree：三处差异，逐条给出 Lean 判定

记 `blind := eqRhigh_A ( = eqRhigh_B)`。

### 3.1 常数：tree 具名 `Chigh` vs blind `∃ C` — **tree ⟹ blind（已证）；blind ⊭ tree**

tree 方向：`Chigh` / `Chigh_pos` 直接充当见证，见 §3.3 的 `tree_implies_A`。
反方向不成立：`blind` 只给出某个未知的 `C`，对具体的 `Chigh m = 6·vectorTameConst m` 一无所知；
一个比 `Chigh` 大的 `C` 满足 blind 却推不出 tree 的界。这是**真非蕴含**，非探针可证的方向，
但最强可得的形式已证（§3.3 `A_implies_tree_exC`）。

### 3.2 导数打包：tree `∃ d, HasDerivAt … ∧ P d` vs blind `DifferentiableAt → P (deriv …)`

**tree 的结论严格更强**，两条都已证：

* tree ⟹ blind 的这一半：`hd.deriv : deriv g t = d`，把 `P d` 改写成 `P (deriv g t)`；
  blind 的 `DifferentiableAt` 前件**根本用不上**（探针里记为 `_hdiff`）。
* tree 还**反过来供给** blind 的前件：`tree_gives_differentiableAt`（`hd.differentiableAt`）。

### 3.3 `HasSmoothSobolevPath`：tree 多一条假设 — **这是唯一的残余，且它正是 A01 的缺口**

`tree ⟹ blind` 需要、也只需要一条残余假设：每个 `ClassicalSolutionR` 都带全阶 `C^∞`-in-time
Sobolev datum 路径。`/tmp/rev130/p2_tree_to_A.lean`：

```lean
theorem tree_implies_A
    (hsm : ∀ {ν : ℝ} {a : Data.SpatialField} {f : Data.SpaceTimeField} {T : ℝ}
      (w : Data.ClassicalSolutionR ν a f T), HasSmoothSobolevPath T w.velocity) :
    BlindRhighA.eqRhigh_A := by
  refine ⟨Chigh, Chigh_pos, ?_⟩
  intro ν hν a ha f hf T w m hm t ht _hdiff
  obtain ⟨d, hd, hbound⟩ :=
    energyIdentityHigh ν a f T hν ha hf (BlowupDensity.Bindings.uniqueness_toA02 w)
      (hsm w) m hm t ht
  have hd' : HasDerivAt (BlindRhighA.hmNormSq m w.velocity) d t := hd
  rw [hd'.deriv]
  exact hbound
```
```
$ lake env lean /tmp/rev130/p2_tree_to_A.lean
'Rev130.tree_implies_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev130.tree_implies_A_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev130.tree_gives_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

注意 `exact hbound` 一步就过：tree 的 `sobolevNormAt` / `gradientSobolevNormAt` 与 A/B 自建的
`hmNorm` / `h2Norm` / `gradHmNorm` / `hmNormSq` 全部 **defeq**（与 `REVIEW_ENERGY_HIGH.md` 的
`rfl` 桥一致），`Data.ClassicalSolutionR → A02.ClassicalSolutionR` 走既有
`Bindings.uniqueness_toA02`（结构体无 `rfl` 桥，逐字段转换，`(uniqueness_toA02 w).velocity = w.velocity` 由 `rfl`）。

**残余假设是否对每个 `ClassicalSolutionR` 可导出？——不可以。** `/tmp/rev130/p4_gap.lean`（负例）：

```lean
theorem hssp_of_classicalSolution … (w : Data.ClassicalSolutionR ν a f T) :
    HasSmoothSobolevPath T w.velocity := by
  intro m
  obtain ⟨G, hGc, hGd⟩ := w.sobolev m
  exact ⟨G, hGd, hGc⟩
```
```
$ lake env lean /tmp/rev130/p4_gap.lean
/tmp/rev130/p4_gap.lean:24:17: error: Application type mismatch: The argument
  hGc
has type
  ContinuousOn G (Ico 0 T)
but is expected to have type
  ContDiffOn ℝ ∞ G (Ico 0 T)
in the application
  ⟨hGd, hGc⟩
EXIT=1
```

即：`ClassicalSolutionR.sobolev`（`Contracts/V1/Data.lean:643-646`）只给**连续** datum 路径，
`HasSmoothSobolevPath`（`Section4/A04/DerivNorm.lean:87`）要 `ContDiffOn ℝ ∞`。这正是
A01 的 `sobolev_smooth`（`research/A01/Spec.lean:180`，split 行 **m1**，size **L**，状态 **gap**）；
`research/A01/REVIEW_M4.md:228-234` 明确写 "It cannot be harvested from `ClassicalSolutionR` —
`ClassicalSolutionR.sobolev` gives only `ContinuousOn`, which is strictly weaker."

### 3.4 反方向：`blind ⟹ tree`（常数取 `∃` 形）— **已证**

`/tmp/rev130/p3_A_to_tree.lean`。关键：tree 多出来的 `HasSmoothSobolevPath` 恰好**化解**
blind 的 `DifferentiableAt` 前件（`hssp_hasDerivAt`，即 `energyIdentityHigh_core` 的第一个 bullet），
于是 blind 的 `deriv` 结论升级成 tree 的 `∃ d, HasDerivAt … ∧ …`：

```lean
theorem hssp_hasDerivAt {T : ℝ} {u : Data.SpaceTimeField}
    (hsm : HasSmoothSobolevPath T u) (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    ∃ d : ℝ, HasDerivAt (BlindRhighA.hmNormSq m u) d t := by
  obtain ⟨G, hGd, hGc⟩ := hsm m
  refine ⟨2 * ⟪G t, deriv G t⟫, ?_⟩
  have h : HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) u r ^ 2) (2 * ⟪G t, deriv G t⟫) t := by
    refine (hasDerivAt_datumNormSq_of_contDiffOn hGc ht).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    rw [sobolevNormAt_eq (hGd r (Ioo_subset_Ico_self hr))]
  exact h

theorem A_implies_tree_exC (hA : BlindRhighA.eqRhigh_A) :
    ∃ C : ℕ → ℝ, (∀ m : ℕ, 0 < C m) ∧
      ∀ (ν) (a) (f) (T), 0 < ν → a ∈ Data.initialClassR → Data.MemForceR f →
        ∀ w : Data.ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0:ℝ) T,
            ∃ d : ℝ, HasDerivAt (fun r => sobolevNormAt (m:ℝ) w.velocity r ^ 2) d t ∧
              (1/2) * d + ν * gradientSobolevNormAt (m:ℝ) w.velocity t ^ 2 ≤
                C m * sobolevNormAt 2 w.velocity t * sobolevNormAt (m:ℝ) w.velocity t *
                    gradientSobolevNormAt (m:ℝ) w.velocity t +
                  sobolevNormAt (m:ℝ) f t * sobolevNormAt (m:ℝ) w.velocity t := …
```
```
$ lake env lean /tmp/rev130/p3_A_to_tree.lean
'Rev130B.hssp_hasDerivAt'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev130B.hssp_differentiableAt'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev130B.A_implies_tree_exC'     depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

### 3.5 判定汇总

| 方向 | 结果 | 探针 |
|---|---|---|
| `tree + A01-m1 ⟹ blind` | **PROVED** | `/tmp/rev130/p2_tree_to_A.lean` `tree_implies_A` |
| `tree ⟹ blind`（单个解，带该解的 `HasSmoothSobolevPath`） | **PROVED** | 同上 `tree_implies_A_pointwise` |
| `tree ⟹ blind`（无残余） | **NOT PROVED** — 障碍是 `ContinuousOn G ≠ ContDiffOn ℝ ∞ G`（错误文本见 §3.3），A01 单元 m1，size L，未证 | `/tmp/rev130/p4_gap.lean` |
| `blind ⟹ tree`（常数存在形） | **PROVED** | `/tmp/rev130/p3_A_to_tree.lean` `A_implies_tree_exC` |
| `blind ⟹ tree`（具名 `Chigh`） | **不成立**（blind 的 `C` 不可辨认） | — |
| `tree` 供给 blind 的 `DifferentiableAt` 前件 | **PROVED** | `tree_gives_differentiableAt` / `hssp_differentiableAt` |

**所以：tree 与 blind 形式上互不蕴含，差额恰好是 A01 的 m1 一条 + 常数的具名/存在。**
在"给定同一个解的 `HasSmoothSobolevPath`"这一前提下，两者**逐点等价**，而 tree 在常数和
可微性断言两处都严格更强。

---

## 4. 保真判决

**判决：tree 的 `energyIdentityHigh` 说的就是论文 `eq:Rhigh`，并且在两位盲写手共同支持的最强读法下
不弱于它。** 逐项：

**tree 更强的地方（都是好事，且都是论文支持的）**

1. **断言可微而非假设可微。** 论文 `:139` 说这些恒等式"是被 Fourier 逼近在光滑存在的紧区间上
   *证成*的"——论文在**断言** `d/dt` 存在。tree 的 `∃ d, HasDerivAt … ∧ …` 对应断言；
   A/B 的 `DifferentiableAt →` 前件对应假设。**tree 的读法更忠实**。
   A 与 B 在各自 md 里都把这条列为"rejected but valid and slightly stronger"，即两人都识别到它。
2. **具名常数。** `Chigh m = A03.outerTameConst m`（eq:tame 的 `6·vectorTameConst m`）+ `Chigh_pos`，
   比 `∃C` 强；而论文的 `C_m` 也确实是一个只依赖 `m` 的具体常数族。

**tree 更弱的地方：只有一条——多出的 `HasSmoothSobolevPath` 假设**

* 相对**论文**：**不是真限制**。论文 `appendix-a-local-theory.tex:72-77` 自己就断言
  "repeated time differentiation gives $C^j_tH^k_x$ regularity for all $j,k$"，
  正是 `HasSmoothSobolevPath` 的内容；`eq:Rhigh` 就写在"compact intervals of smooth existence"上
  （`:139`）。所以 tree 是把论文**已经声明的**时间正则性显式列成假设，而不是新增限制。
* 相对**盲稿**：**是形式上的额外假设**。A/B 只要 `ClassicalSolutionR` + 逐点 `DifferentiableAt`，
  覆盖的解类形式上更大。但——见下——**盲稿形在今天的 tree 里证不出来**。

**A/B 抓到而 tree 漏掉的：无。** 反过来，**tree 抓到而 A/B 漏掉的有两处**：

1. **A/B 的 `DifferentiableAt` 前件太弱，撑不起论文自己的论证。** 论文证 `eq:Rhigh` 的方法是
   "pairing the equation with `u` in `H^m`"（`:129`），需要的是 **datum 路径的导数**
   （`2⟪G t, ∂ₜG t⟫`），不是标量映射 `t ↦ ‖u(t)‖²_{H^m}` 在一点可微。A/B 的前件是那条真假设的
   **推论**（`hssp_differentiableAt` 已证），从它出发无法重建配对。后果：**A/B 的陈述在当前 tree
   里不可证**，要证它必须先补 A01 m1。tree 选的假设正好是论文的那条。
2. **A/B 的 `⊤ ↦ 0` 注意事项只写在 docstring 里，没有对应的有限性事实。** 128 审稿
   （`REVIEW_ENERGY_HIGH.md` §2(d)）证过缺的那一条 `gradientSobolevENorm_velocity_ne_top`
   （`/tmp/rev128/p6_finite.lean`），但它**至今没进 tree**（本分支 `grep` 无结果）。
   这是左端耗散项不退化成 `0 ≤ …` 的唯一保证。

**其余全部一致**：`Ioo 0 T`、`m ≥ 3`、`.toReal`、`‖∇u‖_{H^m}` 用梯度张量范数而非 `‖u‖_{H^{m+1}}`、
未投影的 `f` 切片范数、左结合的三因子乘积、压力项缺席（由 `ClassicalSolutionR.divergence` 在
`pressure_drop` 内消掉）。128 审稿把"第二读者可能分歧的唯二处"点名为梯度范数读法与端点，
两位盲写手独立地都与 tree 同向。**Rule 2 对 eq:Rhigh 关闭。**

---

## 5. 对 A04 合同字段的建议

### 5.1 冻结哪一个陈述：**tree 形，逐字**

`Contracts/V1/EnergyHighPartial.lean` 的 `energyIdentityHigh` 字段照抄
`research/A04/Spec.lean:424-434`（= `EnergyIdentityHigh.lean:145-155`，逐 token 相同），即：

```lean
energyIdentityHigh : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
  0 < ν → a ∈ initialClassR → MemForceR f →
    ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
      ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
        ∃ d : ℝ,
          HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
            (1 / 2) * d + ν * gradientSobolevNormAt (m : ℝ) w.velocity t ^ 2 ≤
              Chigh m * sobolevNormAt 2 w.velocity t *
                  sobolevNormAt (m : ℝ) w.velocity t *
                  gradientSobolevNormAt (m : ℝ) w.velocity t +
                sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t
```

理由（按优先级）：

1. **它已经被证**；盲稿形（`DifferentiableAt` 前件 + `deriv`）在今天的 tree 里**证不出来**，
   会把一条 A01 的 L 级缺口偷渡进合同（§3.3、§4）。
2. **它更忠实**：断言可微、给出常数（§4）。
3. **它蕴含盲稿形**，差额只是 A01 m1（§3.3 已证）；将来 A01 m1 一落地，
   `tree_implies_A` 这 7 行就把盲稿形免费导出，不需要 V2。

**不要**把 `Chigh` 改成字段内的 `∃ C`：record 的两个数据字段 `Chigh : ℕ → ℝ` + `Chigh_pos`
**就是** A/B 那个 `∃ C, (∀ m, 0 < C m) ∧ …` 的 Skolem 化，两位盲写手的读法已经被满足
（`tree_implies_A` 里正是用 `⟨Chigh, Chigh_pos, …⟩` 见证的）。
按 `research/A04/COMPARISON.md:66` / `Spec.lean:325-339`，`Chigh` 在合同里保持 opaque。

### 5.2 需要逐字重述 + `rfl` 桥的辅助定义：三个

| 对象 | `Contracts/V1` 里有吗 | 动作 |
|---|---|---|
| `ClassicalSolutionR`、`initialClassR`、`MemForceR`、`SpatialField`、`SpaceTimeField`、`IsSobolevDatum`、`sobolevENorm` | 有（`Data.lean`） | 直接用 |
| `gradientSobolevENorm` | 有（`TameProduct.lean:192`） | 直接用 |
| `sobolevNormAt` | **无** | 逐字重述 `(sobolevENorm s fun x : Space => u (t, x)).toReal`；桥 `theorem sobolevNormAt_eq : Contract.sobolevNormAt = A04.sobolevNormAt := rfl` |
| `gradientSobolevNormAt` | **无** | 逐字重述 `(TameProduct.gradientSobolevENorm s fun x : Space => u (t, x)).toReal`；同样一条 `rfl` 桥 |
| `HasSmoothSobolevPath` | **无** | 逐字重述（`Spec.lean:247` = `DerivNorm.lean:87`，同一段文本）；`rfl` 桥 |

三条桥 128 审稿已实证可过（`/tmp/rev128/p5_hssp_bridge.lean`，EXIT=0），本 lane 的
`p2`/`p3` 又在它们上面各跑了一遍（`exact hbound` 一步过 = defeq 成立）。
`ClassicalSolutionR` 是 `structure`，按 `CLAUDE.md` 例外走 `Bindings.uniqueness_toA02` 逐字段转换
（本 lane 的 p2/p3 用的就是它，无需新代码）。

### 5.3 scope 串必须披露的内容

1. **`HasSmoothSobolevPath T w.velocity` 是假设，不是结论**；它就是 A01 的 `sobolev_smooth`
   （`research/A01/Spec.lean:180`，split 行 m1，size L），**当前未证**，不可由
   `ClassicalSolutionR.sobolev` 导出（后者只给 `ContinuousOn`）。因此本字段是
   **条件式**的：论文在 `:72-77` 断言了这条正则性，形式化里它还欠着。
   ——这一句是整个字段最重要的披露，必须进 scope。
2. **常数 `Chigh` 保持 opaque**：只断言 `0 < Chigh m`，不断言 `Chigh m = tame.Ctame m`
   （实现里 `rfl` 成立，可作为 Bindings 的 bonus 引理 `Chigh_eq_Ctame`，G2 会要；见
   `REVIEW_ENERGY_HIGH.md` finding 6），也不断言它等于 eq:Rproduct 的 `C_m`。
3. **`‖∇u‖_{H^m}` 是梯度张量的 Sobolev 范数** `(∑_j ‖∂_j u‖²_{H^m})^{1/2}`，
   **不是** `‖u‖_{H^{m+1}}`；阶移 `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}` 明确**不**在断言范围内
   （`TameProduct.lean:51-53` 已把它列为 out of scope）。
4. **时间集是内点 `Ioo 0 T`**，`t = 0` 处什么都不断言（datum 路径在 `Ico 0 T` 上 `C^∞`，
   单侧 `HasDerivWithinAt` 可得但未断言）。
5. **`.toReal` 约定**：四个量都是 `ENNReal.toReal`，`⊤` 会读成 `0`。
   在被量化的类上不会发生（`Continuity.lean:64,73` 的 `sobolevENorm_velocity_ne_top` /
   `sobolevENorm_force_ne_top` 管三个槽），但**第四个槽（梯度）的有限性引理
   `gradientSobolevENorm_velocity_ne_top` 至今不在 tree**（128 审稿 §2(d) 证过，在
   `/tmp/rev128/p6_finite.lean`）。合同 lane 顺手把它落进 `Section4/A04/`，
   否则 scope 必须写明"左端耗散项的非退化性未在库内建立"。
6. **`a ∈ initialClassR` 在证明里未用**（为陈述保真而携带），`0 < ν` 与 `3 ≤ m` 都有余量
   （`0 ≤ ν` / `2 ≤ m` 足够，128 审稿实证），V1 照论文写、余量记在 ATTEMPTS，不改。
7. **不断言**：eq:highcontinuation（下一字段的 `ζ` 正则化）、eq:criterion、eq:mild、
   以及 `t = 0` 端点上的任何内容。

### 5.4 附带产物

`/tmp/rev130/p2_tree_to_A.lean` 的 `tree_implies_A_pointwise` 可以直接作为合同 lane 的
"消费者形"导出（把 `∃ d, HasDerivAt … ∧ …` 折成 `deriv` 形的便利引理），7 行，标准三公理。
不建议进 V1 合同字段（它比主字段弱），但值得留在 `Section4/A04/` 或 Bindings 作 bonus。

---

## 6. 跑过的命令与结果

```
. scripts/lean-env.sh                                   # Lean 4.34.0-rc2
cd verification
LEAN_NUM_THREADS=6 lake build Contracts.V1.Data Contracts.V1.TameProduct        # EXIT=0, 8817 jobs
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.EnergyIdentityHigh \
                              Bindings.Uniqueness                               # EXIT=0, 10016 jobs
lake env lean ../research/A04/blind/rhigh_A.lean         # EXIT=0, 只印 #check
lake env lean ../research/A04/blind/rhigh_B.lean         # EXIT=0, 只印 #check
lake env lean /tmp/rev130/p1_ab.lean                     # EXIT=0, A = B by rfl, 标准三公理
lake env lean /tmp/rev130/p2_tree_to_A.lean              # EXIT=0, 3 个定理, 标准三公理
lake env lean /tmp/rev130/p3_A_to_tree.lean              # EXIT=0, 3 个定理, 标准三公理
lake env lean /tmp/rev130/p4_gap.lean                    # EXIT=1（预期失败）：
    error: Application type mismatch: hGc has type ContinuousOn G (Ico 0 T)
    but is expected to have type ContDiffOn ℝ ∞ G (Ico 0 T)
grep -rn 'gradientSobolevENorm_velocity_ne_top' formalization/ verification/   # 无结果（仍未进 tree）
grep -n 'A04' verification/contracts.json                                      # 无 A04 合同
```

无 `sorry` / `admit` / `axiom` / `native_decide`；所有成功的探针只依赖
`propext` / `Classical.choice` / `Quot.sound`。
