# 审稿 — lane 138（A04 unit **G2b**，`highContinuationIntegral`）

被审对象：`erenup/138-A04-g2b-integral`，相对 `origin/erenup/integration` merge-base 一个 commit
（`92eff17`），四个新增文件，无删改：

```
formalization/NSFormalization/Section4/A04/HighContinuationIntegral.lean  (+174)
research/A04/axioms_high_continuation_integral.lean                       (+51)
research/A04/ATTEMPTS_G2B.md                                              (+104)
research/A04/G1_SPLIT.md                                                  (+13/-1)
```

**结论：ACCEPT-WITH-NOTES。** 定理成立、陈述与 spec 逐 token 相同、与手稿一致、公理标准、门禁全绿。
无阻塞项。两处**记录性错误**必须改（发现 3、发现 4），它们不影响 Lean，但会污染下一条 lane 的计划。

审稿环境：worktree 内 `. scripts/lean-env.sh`，`lake` 一律从 `verification/` 跑，`LEAN_NUM_THREADS=6`；
探针在 `/tmp/rev138/`（易失，报错原文已抄进本文件）。

---

## 1. 编译 / 公理 / 卫生 — **PASS**

```
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.HighContinuationIntegral
Build completed successfully (9953 jobs).            # EXIT=0

$ cd verification && lake env lean ../formalization/.../A04/HighContinuationIntegral.lean
EXIT=0，输出 0 字节（静默，无 warning）

$ cd verification && lake env lean ../research/A04/axioms_high_continuation_integral.lean
EXIT=0
'NSFormalization.Section4.A04.highContinuationIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
（conformance `example` 同时 elaborate 通过，无输出）

$ make check     # EXIT=0（architecture + test_contract_policy 13 tests OK + check_work_queue OK）
$ make test      # EXIT=0，14 个已注册合同全部 "checked; standard logical axioms only"
```

卫生 grep：

```
$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A04/HighContinuationIntegral.lean \
    research/A04/axioms_high_continuation_integral.lean
research/A04/axioms_high_continuation_integral.lean:8   （docstring 里的命令行）
research/A04/axioms_high_continuation_integral.lean:14  （docstring 里的文件名）
research/A04/axioms_high_continuation_integral.lean:30:#print axioms highContinuationIntegral
```

模块本体零命中：无 `sorry`/`admit`/`axiom`/`native_decide`，无 `set_option`，无 `maxHeartbeats`。

**旁证（LESSONS「conformance 会漂移」）**：本 lane 纯增量、未改任何已合陈述，但仍复跑了同节点的四个
conformance 文件，全部 EXIT=0、标准三公理：`axioms_high_continuation`（G2）、`axioms_f1n1`（F1/N1）、
`axioms_z1`（Z1）、`axioms_energy_identity_high`（G1）。

---

## 2. 陈述保真 — **PASS**

### (a) 与 spec field 的机器比对 — token 级**完全相同**

把 `research/A04/Spec.lean` 的 `highContinuationIntegral :` 字段类型与模块 `theorem` 的类型各自
tokenize 后做 `difflib.unified_diff`：

```
spec tokens 163   module tokens 163
IDENTICAL token stream
```

连命名空间限定符都没有差别（两边都用 `open` 后的裸名）。conformance 文件里的 `example` 又独立复核了
一遍（它把 spec 字段照抄成 formalization 词汇，由 `highContinuationIntegral` 直接 `exact` 掉）。

### (b) 与手稿的比对 — **一致**

行号现查（LESSONS「论文行号会代代相传」）：

```
$ grep -n 'label{eq:highcontinuation}' paper/sections/*.tex
paper/sections/appendix-a-local-theory.tex:142
```

`:141-145` 是从「followed by $\zeta\downarrow0$, imply」到 `\end{equation}` 的整块，引用正确。手稿：

```
 (\norm{u}_{H^m})'
 \le C_{m,\nu}\norm{u}_{H^2}^2\norm{u}_{H^m}+\norm{f}_{H^m}.
```

* **被积函数形状对**：`Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 * sobolevNormAt (m:ℝ) w.velocity s
  + sobolevNormAt (m:ℝ) f s`。`^2` 只挂在 `H²` 那个因子上；对 `‖u‖_{H^m}` 是**一次**的，不是平方。
  这正是 Grönwall（线性版）能吃的形状，也正是手稿写的。
* **`ζ↓0` 之后改成积分形式**是对的，且模块 docstring 把理由写清楚了：极限后左边是 `‖u‖_{H^m}`，
  在 `u` 于 `H^m` 中取零的时刻不必可导，`(\cdot)'` 是简写。这不是偷懒——`sqrt_le_primitive_linear`
  是**无** `E t₀ = 0` 假设的真 `ζ↓0` 论证（正则化 `√(E+δ²)`、证差单调、再 `δ↓0`），不是把微分式
  改写成积分式的空转。
* **端点集 `0 ≤ t₀ ≤ t < T` 正确，且比 `Ioo` 强**。
  - `t₀ = 0` 可取：`‖u(0)‖_{H^m}` 有限，因为 `ClassicalSolutionR.sobolev m` 在整个 `Ico 0 T`（含 0）
    给出 datum，`sobolevNormAt_eq` 把 `.toReal` 定到 `‖G 0‖`。
  - `HasSmoothSobolevPath` **不在端点被用**：它只经 `deriv_normSq_absorbed` 进入，而后者要求
    `s ∈ Ioo 0 T`；证明里由 `s ∈ Ioo t₀ t` 经 `⟨lt_of_le_of_lt ht₀ hs.1, lt_trans hs.2 htT⟩` 得到。
    端点处干活的是 N1 的 `ContinuousOn … (Ico 0 T)`（`sqrt_le_primitive_linear` 的
    `ContinuousOn (Icc t₀ t)` 假设）+ `AntitoneOn (Icc t₀ t₁)`。所以 `Ico`（含 0）是正确的、
    而且是**免费**的：微分信息只在开区间用，端点靠连续性补齐。
  - `0 ≤ t₀` 是**承重**的：`t₀ < 0` 时 `Icc t₀ t ⊄ Ico 0 T`，连续性断掉，而且负时刻没有 datum、
    `sobolevENorm` 可能是 `⊤`、`sobolevNormAt` 读成 junk `0`，结论会变成假命题而不是空洞命题。
  - `t < T` 严格，正确（`t = T` 解未必存在）。
  - `t₀ = t` 退化情形不需特判：`sqrt_le_primitive_linear` 收 `t₀ ≤ t₁`，`Ioo t₀ t = ∅` 让四个
    内点假设空洞成立。

### (c) `IntervalIntegrable` 合取项：**被断言、被证明**，不是被假设 — **PASS**

它出现在**结论**里（`… ∧ …` 的第一项），由 N1 的
`intervalIntegrable_highContinuationIntegrand`（`Continuity.lean:132`）一次应用给出，链条是
`ContinuousOn.intervalIntegrable ← uIcc_of_le ← Icc t₀ t ⊆ Ico 0 T ← 三个 sobolevNormAt 的连续性`。
所以 Mathlib「不可积 ⇒ 积分 junk `0`」的陷阱被关掉了：积分是真 Lebesgue 积分。

**`⊤ ↦ 0` 陷阱**：`sobolevNormAt` 是 `.toReal`，但在被量化的类上取不到 `⊤`。
关键不是四个 `_ne_top` 引理中的哪一个被调用——**本模块一个都没直接调用**——而是
`continuousOn_sobolevNormAt_velocity` / `_force` 内部走的
`continuousOn_sobolevNormAt_of_datumPath → sobolevNormAt_eq`，把 `sobolevNormAt s u t` 定成了
**datum 范数 `‖G t‖`**（`ENNReal.toReal_ofReal (norm_nonneg _)`），根本没有 `⊤` 的余地。
命名的 `sobolevENorm_velocity_ne_top` / `sobolevENorm_force_ne_top`（`Continuity.lean:64,73`）是
同一事实的独立记账，供合同 scope 引用。

回答简报的问题：**`gradientSobolevENorm_velocity_ne_top` 在这里用不上**，被积函数里没有梯度范数。
它属于 G1（`energyIdentityHigh` 的耗散项 `ν‖∇u‖²_{H^m}`）的闭包，本模块经
`deriv_normSq_absorbed` **继承**那份有限性，不需要也不应该在这里重提。四个之中与 G2b 相关的
只有 velocity / force 两个，而且是以 `sobolevNormAt_eq` 的形式间接生效。

### (d) 承重表（每一条都跑了探针，不是读代码猜的）

| 假设 | 判定 | 证据 |
|---|---|---|
| `0 < ν` | **承重** | 减弱成 `0 ≤ ν` 后同一证明三处报错（下）。且 `ν = 0` 时 `Cgron m 0 = 0`（除法 junk），陈述会变成更强且**假**的命题 |
| `a ∈ initialClassR` | 语法上承重，数学上是**继承的冗余** | 删掉后 `Unknown identifier 'ha'`（两处），说明证明确实用它；但它只是被透传给 `deriv_normSq_absorbed → energyIdentityHigh`，而 V1 合同 scope 已披露 `energyIdentityHigh` 的证明里 `a ∈ initialClassR` 是 slack。本 lane 没有**新增**冗余 |
| `MemForceR f` | **承重** | 两处：`intervalIntegrable_highContinuationIntegrand hf`（可积性）与 `deriv_normSq_absorbed … hf` |
| `MemL1Hm f` | **未用**，且**可从 `MemForceR` 推出** | 见下 |
| `HasSmoothSobolevPath` | **承重** | 经 `deriv_normSq_absorbed`（内点导数） |
| `3 ≤ m` | **承重** | 减弱成 `2 ≤ m` 后两处 type mismatch（下） |
| `0 ≤ t₀` / `t₀ ≤ t` / `t < T` | **承重** | 分别给 `Icc t₀ t ⊆ Ico 0 T`（连续性）、`Ioo t₀ t ⊆ Ioo 0 T`（内点导数）、`sqrt_le_primitive_linear` 的 `t₀ ≤ t₁` |

`3 ≤ m → 2 ≤ m`（`/tmp/rev138/p_m2.lean`，`set_option autoImplicit false`，原证明逐字不变）：

```
$ lake env lean /tmp/rev138/p_m2.lean        # EXIT=1
p_m2.lean:42:66: error: Application type mismatch: The argument
  hm
has type
  2 ≤ m
but is expected to have type
  3 ≤ m
in the application
  @deriv_normSq_absorbed ν a f T hν ha hf w hpath m hm
p_m2.lean:52:64: error: ... @deriv_normSq_absorbed_deriv ν a f T hν ha hf w hpath m hm
```

`0 < ν → 0 ≤ ν`（`/tmp/rev138/p_nu0.lean`）——简报预期的 `Cgron` 那一处确实出现：

```
$ lake env lean /tmp/rev138/p_nu0.lean       # EXIT=1
p_nu0.lean:42:47: error: ... deriv_normSq_absorbed hν            (0 ≤ ν vs 0 < ν)
p_nu0.lean:52:45: error: ... deriv_normSq_absorbed_deriv hν
p_nu0.lean:62:42: error: Application type mismatch: The argument
  hν
has type
  0 ≤ ν
but is expected to have type
  0 < ν
in the application
  Cgron_pos m ν hν
```

删掉 `MemL1Hm f`（`/tmp/rev138/p_nol1.lean`，陈述里去掉该假设、`intro` 去掉 `_hf1`、证明其余逐字不变）：

```
$ lake env lean /tmp/rev138/p_nol1.lean      # EXIT=0（无输出）
```

即**不用它也证得出**，`MemL1Hm` 确认为纯保真假设。更强的一点（worker 未记）：它甚至**不是独立假设**——
树里已有 `A04.memL1Hm_of_memForceR : MemForceR f → MemL1Hm f`（`Forcing.lean:140`，unit F1a），
所以 `MemL1Hm f` 在 `MemForceR f` 之后是可推出的冗余。见发现 5。

删掉 `a ∈ initialClassR`（`/tmp/rev138/p_noha.lean`）：

```
$ lake env lean /tmp/rev138/p_noha.lean      # EXIT=1
p_noha.lean:42:50: error(lean.unknownIdentifier): Unknown identifier `ha`
p_noha.lean:52:48: error(lean.unknownIdentifier): Unknown identifier `ha`
```

按 LESSONS 的标准，这**只证明该 lane 的证明路径消费了它**，不证明数学上必要；必要性问题在 G1
（`energyIdentityHigh`）那层，V1 scope 已披露为 slack，不是本 lane 的债。

### (e) 非空洞性 — **PASS**（worker 的「树里没有 zero witness」结论不完整，见发现 6）

按简报要求重建了 `zeroSol`（`research/D01/REVIEW_SL8_ASSEMBLY.md` 附录 A + `REVIEW_ENERGY_HIGH.md`
的 `path_zero`），并在本模块的 import 闭包里**实例化被审定理本身**
（`/tmp/rev138/p_vacuity2.lean`，`ν=1, a=0, f=0, T=1, m=3, t₀=0, t=1/2`）：

```lean
theorem g2b_on_zeroSol :
    IntervalIntegrable (fun s => Cgron 3 1 * sobolevNormAt 2 (zeroSol 1).velocity s ^ 2 *
        sobolevNormAt ((3:ℕ):ℝ) (zeroSol 1).velocity s + sobolevNormAt ((3:ℕ):ℝ) (0:SpaceTimeField) s)
        volume 0 (1/2) ∧ … :=
  highContinuationIntegral 1 0 0 1 one_pos zero_mem_initialClassR memForceR_zero
    (memL1Hm_of_memForceR memForceR_zero) (zeroSol 1) (path_zero 1) 3 le_rfl 0 (1/2)
    le_rfl (by norm_num) (by norm_num)

theorem zeroSol_norm_zero (s r : ℝ) : sobolevNormAt r (zeroSol 1).velocity s = 0 := …
```
```
$ lake env lean /tmp/rev138/p_vacuity2.lean
EXIT=0
'Rev138V.g2b_on_zeroSol'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev138V.zeroSol_norm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

即**整包假设（含 `0 ≤ t₀ ≤ t < T`、`MemL1Hm`、`HasSmoothSobolevPath`）是可满足的**，
注意 `MemL1Hm` 这里是用 `memL1Hm_of_memForceR` 免费拿到的——顺便实证了发现 5。
零解上两边都退化成 `0 ≤ 0 + 0`（`zeroSol_norm_zero`），所以这个 witness 只证「非空洞」，
不证「不平凡」。

**对非零解是否平凡成立？否。** 树里还没有非零 `ClassicalSolutionR`（A01 的活），所以我改证结论
**形状**本身不是恒真式（`/tmp/rev138/p_content.lean`）：取 `K ≡ 1/2`、`b ≡ 0`、范数按 `exp` 增长，

```lean
theorem shape_not_tautology :
    ¬ (Real.exp 1 ≤ Real.exp 0 + ∫ s in (0:ℝ)..1, ((1/2 : ℝ) * Real.exp s + 0)) := …
-- 'Rev138C.shape_not_tautology' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`e ≈ 2.718 > 1 + (e−1)/2 ≈ 1.859`：增长率 1 超过系数 1/2 就被拒。所以
`‖u(t)‖ ≤ ‖u(t₀)‖ + ∫(C‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m})` 是对 `‖u‖_{H^m}` 增长率的**真约束**
（正是 Grönwall 在 R41 里要消费的那条），不是 `‖u(t)‖ ≤ 任何东西 + 非负积分` 式的送分题。

---

## 3. 与树的一致性 — **PASS**，两条 note

* **imports**：`A04.HighContinuation` + `A04.Continuity`，两个都被消费（前者出 `Cgron`/`Cgron_pos`/
  `deriv_normSq_absorbed`/`_deriv`，并经 `Regularized` 传递 `sqrt_le_primitive_linear`；后者出
  `intervalIntegrable_highContinuationIntegrand` 与两个 `continuousOn_*`）。没有多余 import，
  没有新的 Mathlib import。
* **零重述定义**：模块只有一个 `theorem`，没有任何 `def`/`structure`，不存在重述漂移面。
  `NSFormalization` lib 用 glob（`lakefile.toml` 无 `roots`），新模块自动进目标，不需要登记。
* **`A04.Cgron` 显式传参**是必要的：`intervalIntegrable_highContinuationIntegrand` 自带一个
  `(Cgron : ℕ → ℝ → ℝ)` **参数**（N1 当时刻意不依赖 `Cgron` 的值），不显式给会被局部绑定遮蔽的风险
  在别处出现。写法正确。

### 发现 1（低，note）— 收尾的 `calc` 是**稳的**，但基于一个**错误的理由**，而且可以缩到 3 行

ATTEMPTS 的「陷阱 2」声称 `sqrt_le_primitive_linear` 的结论在 `hmain` 里带着未 β 归约的
applied lambda，所以「`rw … at hmain` 可能 miss」，因此必须走 `calc` 让 defeq 吃掉 β。
**这一条不成立**（见发现 3 的复现）：`hmain` 存进 local context 时已经完全 β 归约。

对 lane 本身无害——`calc` 的中间步 `:= hmain` 是**语法**匹配而不是靠 defeq 兜底，因此
**不脆弱**：若上游 `sqrt_le_primitive_linear` 改形状，这里会给出清晰的 type mismatch 而不是
静默 defeq 漂移。只是 12 行写了 3 行的事（`/tmp/rev138/t2c.lean` 用
`rw [Real.sqrt_sq (hvnn t), Real.sqrt_sq (hvnn t₀), hintEq] at hmain; exact hmain` 通过，EXIT=0）。
**不要求改代码**（已冻结的风险为零，且现写法可读性更好）；要求改 ATTEMPTS 里的理由（发现 3）。

### 发现 2（低，MAINT note）— `regularizedNormDerivative`（G2）在链上仍是**孤儿**

```
$ grep -rn 'regularizedNormDerivative' formalization/ verification/ research/ --include='*.lean' | grep -v Spec.lean
... HighContinuation.lean:183:theorem regularizedNormDerivative     （定义处）
... HighContinuation.lean:5,40,128,165                              （docstring）
... DerivNorm.lean:8                                                （docstring）
... Contracts/V1/EnergyHighPartial.lean:60                          （out-of-scope 披露）
... research/A04/axioms_high_continuation.lean:12,17,35,37,39,51     （公理审计）
```

**零个证明消费者**。G2b 没有经过它：G2b 直接吃 `deriv_normSq_absorbed` +
`sqrt_le_primitive_linear`（等于把 G2 的 `ζ` 步骤在 `Regularized.lean` 那一层重做了一遍，
而且是带 `δ↓0` 的完整版）。这不是 lane 138 的缺陷（`Spec.lean` 把两者列为**并列**字段），
但直接影响 V2 的注册决定，见第 5 节。

---

## 4. ATTEMPTS 的诚实度 — 三个「设计规避的陷阱」，**两真一假**

### 陷阱 1（`hbnonneg` 给成速度范数而非力范数）— **真**

`/tmp/rev138/t1_hbnonneg.lean`（把 `(fun s _ => ENNReal.toReal_nonneg)` 换成 `(fun s _ => hvnn s)`）：

```
$ lake env lean /tmp/rev138/t1_hbnonneg.lean      # EXIT=1
t1_hbnonneg.lean:63:16: error: Type mismatch
  hvnn s
has type
  0 ≤ sobolevNormAt (↑m) w.velocity s
but is expected to have type
  0 ≤ sobolevNormAt (↑m) f s
```

### 陷阱 3（被积函数改写必须走 `intervalIntegral.integral_congr`，不能 binder 下 `rw`）— **真**

`/tmp/rev138/t3_rw_binder.lean`（把 `hintEq` 的证明换成 `rw [Real.sqrt_sq (hvnn _)]`）：

```
$ lake env lean /tmp/rev138/t3_rw_binder.lean     # EXIT=1
t3_rw_binder.lean:75:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  √(sobolevNormAt (↑m) w.velocity ?m.1027 ^ 2)
in the target expression
  ∫ (s : ℝ) in t₀..t,
      Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 * √(sobolevNormAt (↑m) w.velocity s ^ 2) + sobolevNormAt (↑m) f s =
    ∫ (s : ℝ) in t₀..t,
      Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 * sobolevNormAt (↑m) w.velocity s + sobolevNormAt (↑m) f s
```

### 发现 3（中，**记录必须改**）— 陷阱 2（`rw … at hmain` 会 miss）**是假的**

`/tmp/rev138/t2b.lean`：原证明到 `hmain` 为止逐字不变，然后**直接** `rw … at hmain`：

```
$ lake env lean /tmp/rev138/t2b.lean
EXIT=0
t2b.lean:9:8: warning: declaration uses `sorry`      ← 只有我留的收尾 sorry，rw 本身成功
```

`/tmp/rev138/t2d.lean` 用 `trace_state` 打出 `hmain` 的真实类型，**完全 β 归约**：

```
hmain :
  √(sobolevNormAt (↑m) w.velocity t ^ 2) ≤
    √(sobolevNormAt (↑m) w.velocity t₀ ^ 2) +
      ∫ (s : ℝ) in t₀..t,
        Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 * √(sobolevNormAt (↑m) w.velocity s ^ 2)
          + sobolevNormAt (↑m) f s
```

而且整条朴素路线是通的（`/tmp/rev138/t2c.lean`，EXIT=0）。
**要求**：`ATTEMPTS_G2B.md` 的「Traps designed around」第 2 条改写为「`hmain` 在本 pin 下已 β 归约，
`rw … at hmain` 可行（探针 `t2b`/`t2c`）；选 `calc` 是为了让中间步语法匹配、上游改形状时报错清晰，
不是因为 β 不归约」。理由：LESSONS 里已有两条「错误结论代代相传」的教训（117 的论文行号、
073 的假堵点），这条若留着，下一个用 `sqrt_le_primitive_linear` 的 lane（C01/I01 的 `ζ` 步）
会照抄 12 行 `calc` 并写进自己的 ATTEMPTS。**不要**把它升级成 `logs/LESSONS.md` 的一行——它是假的。

### 发现 4（中，**记录必须改**）— `G1_SPLIT.md` 新增段里的一句话与事实相反

lane 138 往 `G1_SPLIT.md` 末尾加了：

> `regularizedNormDerivative`'s consumer (`highContinuationIntegral`) now exists, as the plan
> required before freezing the spelling.

**不成立**。G2b 不消费 `regularizedNormDerivative`（发现 2 的 grep）。原计划设的门槛
（「等 G2b 落地、`regularizedNormDerivative` 有了消费者再冻结它的拼写」）**没有被满足**，
lead 在开 V2 lane 时必须按未满足处理。要求把那句改成事实陈述：
「G2b 已落地，但它绕过了 `regularizedNormDerivative`，直接消费 `deriv_normSq_absorbed` +
`sqrt_le_primitive_linear`；后者至今零消费者。」

### 发现 5（低，V2 note）— `MemL1Hm` 不只是「未用」，而是**可推导**

ATTEMPTS 写「present only for spec fidelity」，对但不全：树里的
`A04.memL1Hm_of_memForceR`（`Forcing.lean:140`，unit F1a）已经给出 `MemForceR f → MemL1Hm f`，
所以它在 `MemForceR f` 之后是**逻辑冗余**，不是一个独立的保真钩子。
（我的零解实例化就是用它免费造出来的。）V2 的处理建议见第 5 节。

### 发现 6（低，记录完整性）— 「树里没有 zero witness」的结论下得太早

ATTEMPTS 末尾：

> No zero-solution instantiation: no `ClassicalSolutionR` zero witness exists in the tree
> (grep of `research/A04`, `Section4/A04` for `zero.*[Ss]olution` empty), so the "if cheap"
> instantiation is skipped.

字面为真（`formalization/` 里确实没有已提交的 `zeroSol` **def**），但 grep 范围漏了
`research/D01/REVIEW_SL8_ASSEMBLY.md` 附录 A 与 `research/A04/REVIEW_ENERGY_HIGH.md`、
`REVIEW_HIGH_CONTINUATION.md`、`REVIEW_HPR.md`、`REVIEW_CONTRACT.md` 里已经重建过**四次**的
`zeroSol`/`memForceR_zero`/`path_zero`/`zero_mem_initialClassR`。我按第 (e) 节重建，
**十几分钟**、一次通过。这与 LESSONS「否定性结论要按文件名 + 定理名 + docstring 三路 grep」同类：
本例还要加一路——**同节点的 REVIEW/ATTEMPTS 附录**。
（顺带：这已经是第五次手抄同一份 `zeroSol`。建议 lead 开一条 MAINT，把它作为
`research/A04/probes/zero_solution.lean` 或 `Section4/A02/ZeroSolution.lean` 落地一次，
以后所有非空洞性探针直接 import；`ATTEMPTS_SIMP.md:688` 已经把它列为「shared unlock」。）

---

## 5. 给 lead：A04 **V2** 合同 lane 的确切内容

`verification/Contracts/V2/EnergyHighPartial.lean`，沿用树里 V2 的既有形状
（`Contracts/V2/MaximalPartial.lean` 等：`import Contracts.V1.<同名>` + `structure …V2API extends …`）。

### 5.1 imports 与需要重述的概念

只需 `import Contracts.V1.EnergyHighPartial`（它已 import `Contracts.V1.Data` 与
`Contracts.V1.TameProduct`）。import 政策（`check_contracts.py`：只许 `Mathlib`/`Lean`/`Init`/`Contracts.*`）
自动满足，不碰 009 的白名单放宽。

**V1 已有、直接继承、不要重抄**：`sobolevNormAt`、`gradientSobolevNormAt`、`HasSmoothSobolevPath`
（V1 §1 的三个重述，`Bindings/EnergyHighPartial.lean:48,55,62` 已有三条 `rfl` 桥）；
`ClassicalSolutionR`、`initialClassR`、`MemForceR`、`SpatialField`、`SpaceTimeField`（`Contracts.V1.Data`）。

**Mathlib 自带、不需要重述、不需要桥**：`IntervalIntegrable`、`intervalIntegral`（`∫ s in t₀..t, ·` 记号）、
`MeasureTheory.volume`、`Real.sqrt`、`HasDerivAt`、`Set.Ioo`。

**需要新增重述 + `rfl` 桥的，只有一个：`MemL1Hm`**（若保留该假设）。
`Contracts/V1/Data.lean` 有 `IsSobolevPath:174`、`bochnerDatumENorm:205`、`forceSobolevENorm:225`、
`forceSobolevENormL1:231`，但**没有** `MemL1Hm`。所以 V2 里写一行

```lean
/-- `research/A04/Spec.lean:268` `MemL1Hm`（`Section4/A04/Forcing.lean:110`） -/
def MemL1Hm (f : SpaceTimeField) : Prop := ∀ m : ℕ, forceSobolevENormL1 (m : ℝ) f ≠ ⊤
```

并在 `Bindings/EnergyHighPartial.lean`（或新的 `Bindings/EnergyHighPartialV2.lean`）加第四条桥
`… .MemL1Hm = NSFormalization.Section4.A04.MemL1Hm := rfl`。
`Cgron` 作为**不透明字段**（`Cgron : ℕ → ℝ → ℝ` + `Cgron_pos : ∀ m ν, 0 < ν → 0 < Cgron m ν`）
**不需要**重述也不需要桥——值 `(Chigh m)²/(4ν)` 只在 binding 里以 bonus 定理
`energyHighPartialV2_Cgron_eq : api.Cgron = fun m ν => Chigh m ^ 2 / (4 * ν) := rfl` 出现
（与 V1 的 `energyHighPartial_Chigh_eq_Ctame` 同样式）。

**替代方案（推荐考虑）**：`highContinuationIntegral` 字段**去掉 `MemL1Hm f`**（发现 5：它未被使用，
且由 `MemForceR f` 推出）。这样 V2 **一个重述、一条桥都不需要新增**，合同面最小。
代价：与 `research/A04/Spec.lean` 的草稿字段不再 token 相同——需要在 scope 里明写
「草稿的 `MemL1Hm f` 由 `MemForceR f` 经 `A04.memL1Hm_of_memForceR`（unit F1a）推出，
故 V2 只收 `MemForceR`；`research/A04/axioms_high_continuation_integral.lean` 保留草稿形状的
conformance example」。两条路我都验证过可编（`/tmp/rev138/p_nol1.lean`）。
**我的建议：保留 `MemL1Hm`**，理由是规矩 2（陈述保真第一）优先于合同面大小，且它带手稿里
「`f` 的 `L¹_t H^m` 约束」这条信息；把「它冗余」写进 scope 即可。

### 5.2 字段清单

```lean
structure EnergyHighPartialV2API extends EnergyHighPartialAPI where
  Cgron : ℕ → ℝ → ℝ                                   -- 不透明
  Cgron_pos : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < Cgron m ν
  regularizedNormDerivative : …                        -- Spec.lean:459-470（见 5.4）
  highContinuationIntegral : …                         -- Spec.lean:471-494
```

binding 目标：`A04.Cgron`、`A04.Cgron_pos`、`A04.regularizedNormDerivative`
（`HighContinuation.lean:183`）、`A04.highContinuationIntegral`
（`HighContinuationIntegral.lean`）。Tests 沿用 `Tests/EnergyHighPartial.lean` 的模板另开
`Tests/EnergyHighPartialV2.lean`（`warningAsError = true`，不许 import `Formal.*`）。

### 5.3 scope 必须披露的内容（在 V1 scope 的基础上追加）

1. **`Cgron` 不透明**：合同只断言 `0 < Cgron m ν`（`ν > 0` 时），**不**断言 `Cgron = (Chigh m)²/(4ν)`。
   手稿对 `C_{m,ν}` 没有给公式；该值只在 binding 里以 `rfl` bonus 出现。
2. **`ν = 0` 处的 junk**：`Cgron m 0 = 0`（Lean 除以零），所以 `0 < ν` 不可减弱为 `0 ≤ ν`——
   否则陈述变成更强且**假**的命题。本次探针 `p_nu0.lean` 与 135 审稿的
   `p7_dup.lean`（`example (m : ℕ) : Cgron m 0 = 0 := by simp [Cgron]`）双向佐证。
3. **`highContinuationIntegral` 是 `ζ↓0` 之后的积分形，不是微分形**，理由（极限后 `‖u‖_{H^m}` 在
   零点不必可导；这是 Grönwall 唯一消费的形状）要照抄 spec docstring 进 scope。
4. **`IntervalIntegrable` 合取项是被断言的**（不是假设），由 N1 从连续性证出；因此积分是真 Lebesgue
   积分而非 Mathlib 的 junk `0`。
5. **`.toReal` 的 `⊤ ↦ 0`**：两个 `sobolevNormAt` 槽位由 `Continuity.lean:64,73` 覆盖
   （velocity / force），**梯度槽位在本字段不出现**，不要照抄 V1 scope 里那句
   `gradientSobolevENorm_velocity_ne_top`。
6. **端点**：`0 ≤ t₀ ≤ t < T`；`t₀ = 0` 在内（`Ico`，不是 `Ioo`），端点由连续性而非
   `HasSmoothSobolevPath` 覆盖；`t = T` 不在内。
7. **条件性继承**：整个 V2 与 V1 一样 **conditional on `HasSmoothSobolevPath`**（A01 unit m1，
   尚未证明）。这是 A04 最重要的一条披露，V2 不得弱化。
8. **`MemL1Hm f` 冗余**（若保留）：由 `MemForceR f` 经 `A04.memL1Hm_of_memForceR` 推出，
   证明未消费；保留是为保真。
9. **`a ∈ initialClassR` 是 slack**（继承自 V1 的披露）。
10. **仍不在范围内**：eq:criterion 本身、Grönwall 的续接推论（`Spec.lean` 下一字段，
    `appendix-a-local-theory.tex:146-147`）、eq:mild / mild 语义 / 定理 4.1 的 first-crossing。

### 5.4 `regularizedNormDerivative` 要不要注册？——**要，但必须改口径**

事实：G2b **不**消费它（发现 2、发现 4），当初设的「等消费者出现」门槛并未满足。
尽管如此我建议**照常注册**，理由三条：

* 它是手稿 `appendix-a-local-theory.tex:139-145` 的**中间显式陈述**（「除以正则化范数
  `(‖u‖²_{H^m}+ζ²)^{1/2}`，然后 `ζ↓0`」），`Spec.lean` 把它与积分形并列为两个字段，
  不是一个被淘汰的中间步。规矩 2 的口径是「合同陈述要覆盖论文说的那件事」，不是「只覆盖被下游用到的」。
* 它已经证完、标准三公理、conformance 在（`axioms_high_continuation.lean`），注册的边际成本为零；
  不注册反而要在 V2 scope 里解释「为什么手稿写了的一步不在合同里」。
* 手稿的同一 `ζ` 手法在 `02-preliminaries.tex:152`、`04-whole-space.tex:103`、`:121` 还要用三次
  （`COMPARISON.md` §4 unit Z1 的记账），C01/I01 落地时它是现成的对照。

但 scope 里必须**明写**：「`regularizedNormDerivative` 与 `highContinuationIntegral` 是**并列**的两个
手稿显式陈述，后者**不经过**前者——它直接走 `deriv_normSq_absorbed` + Z1 的
`sqrt_le_primitive_linear`（带 `δ↓0`），因此 `regularizedNormDerivative` 目前在树里**零消费者**。」
这样冻结的是一个诚实的孤儿，而不是一个被谎称有消费者的字段。

**顺带的 MAINT 账**（135 审稿发现 3 已记，这里确认仍然成立）：`Regularized.lean` 的
`regularized_sqrt_hasDerivWithinAt` / `regularized_sqrt_deriv` 也仍是零消费者。
建议 lead 把「Z1 的导数半边 + G2 的 `regularizedNormDerivative`」合成一条 MAINT 观察项，
等 C01/I01 的 `ζ` 步落地后一起裁决，不要现在删。

---

## 6. 跑过的命令与结果（汇总）

```
cd verification && lake build NSFormalization.Section4.A04.HighContinuationIntegral   EXIT=0 (9953 jobs)
cd verification && lake env lean ../formalization/.../HighContinuationIntegral.lean   EXIT=0, 0 bytes
cd verification && lake env lean ../research/A04/axioms_high_continuation_integral.lean
                                                                   EXIT=0, 标准三公理 + example 通过
cd verification && lake env lean ../research/A04/axioms_{high_continuation,f1n1,z1,energy_identity_high}.lean
                                                                   EXIT=0 ×4（无漂移）
make check                                                         EXIT=0
make test                                                          EXIT=0（14 个合同 standard axioms）
python3 (difflib) spec field vs theorem type                       163/163 tokens, IDENTICAL
grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' 模块零命中
/tmp/rev138/p_m2.lean      (3≤m → 2≤m)                             EXIT=1（2 处 type mismatch）✔ 承重
/tmp/rev138/p_nu0.lean     (0<ν → 0≤ν)                             EXIT=1（3 处，含 Cgron_pos）✔ 承重
/tmp/rev138/p_nol1.lean    (删 MemL1Hm)                            EXIT=0                     ✔ 未用
/tmp/rev138/p_noha.lean    (删 a ∈ initialClassR)                  EXIT=1（unknown ident ha）  ~ 语法承重
/tmp/rev138/p_vacuity2.lean(zeroSol 实例化 + 零解退化)             EXIT=0，标准三公理          ✔ 非空洞
/tmp/rev138/p_content.lean (结论形状非恒真)                        EXIT=0，标准三公理          ✔ 不平凡
/tmp/rev138/t1_hbnonneg.lean (陷阱 1)                              EXIT=1  ✔ 真
/tmp/rev138/t2b.lean, t2c.lean, t2d.lean (陷阱 2)                  EXIT=0  ✘ 陷阱不成立
/tmp/rev138/t3_rw_binder.lean (陷阱 3)                             EXIT=1  ✔ 真
git status --short                                                 空（worktree 干净）
```

---

## 7. 裁决

**ACCEPT-WITH-NOTES.** 可以合入 `erenup/integration`。

合入**前**要求 worker（或 lead 代改，两处都是 md）：

* **发现 3**：`ATTEMPTS_G2B.md` 的陷阱 2 改写为「`hmain` 已 β 归约，`rw … at hmain` 可行；
  选 `calc` 是为语法匹配/报错清晰」，并**不要**把它写进 `logs/LESSONS.md`。
* **发现 4**：`G1_SPLIT.md` 末段的「`regularizedNormDerivative` 的消费者现在存在」改为事实
  （G2b 绕过它，它仍零消费者）。

合入**后**（不阻塞）：

* 发现 5 / 5.1：V2 lane 按第 5 节执行，`MemL1Hm` 建议保留 + scope 披露冗余。
* 发现 6：开一条 MAINT 把 `zeroSol` 落地一次（第五次手抄了）。
* 发现 2 / 5.4：`regularizedNormDerivative` 与 Z1 导数半边的「零消费者」并成一条 MAINT 观察项。
