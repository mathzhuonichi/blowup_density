# REVIEW_CONTRACT — 审稿：lane 133-A04-energy-high-contract

对象：分支 `erenup/133-A04-energy-high-contract`，单个 commit `89ca998`，merge-base
`56b5757`。注册第一个 A04 合同 `A04.energy_high_partial`（eq:Rhigh，
`paper/sections/appendix-a-local-theory.tex:132-137`）。

**判决：ACCEPT-WITH-NOTES。** 四项检查全部通过：合同陈述与 tree 定理、spec 字段**逐字节相同**，
三条 `rfl` 桥我独立用 `Eq.refl` 重证（双向），假设包在合同层面被我完整实例化（零解 + 
`HasSmoothSobolevPath` 见证），记录的负例 N1 逐字复现。四条 notes 见 §5，其中 **finding 1 建议
合入前修**（一个 research 文件加两行，不动合同）。

环境 `. scripts/lean-env.sh`（Lean 4.34.0-rc2），`lake` 一律从 `verification/` 跑，
`LEAN_NUM_THREADS=6`。探针在 `/tmp/rev133/`。

---

## 1. 编译与政策 — **PASS**

```
$ cd verification && lake build Tests.EnergyHighPartial
info: Tests/EnergyHighPartial.lean:17:0: Contract BlowupDensity.Tests.checkedEnergyHighPartial:
      checked; standard logical axioms only
Build completed successfully (10023 jobs).                                    EXIT=0

$ lake build NSFormalization.Section4.A04.GradientFiniteness
Build completed successfully (9884 jobs).                                     EXIT=0
$ lake env lean ../formalization/NSFormalization/Section4/A04/GradientFiniteness.lean
(silent)                                                                      EXIT=0

$ make check
python3 experiments/test_contract_policy.py   → Ran 13 tests … OK
python3 experiments/check_work_queue.py       → 30 work items: ownership, contract
                                                registration and task cards consistent.
                                                                              EXIT=0

$ make test        → 23 行 "checked; standard logical axioms only"（grep -c = 23）
$ make test-mutations
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.

$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
registered_contracts: 23
base_compatibility_checked: True                                              EXIT=0
```

### 未改动既有文件 — 确认

```
$ git diff 56b5757 --name-status
M  collaboration/TASKS.md
M  collaboration/tasks/A04.md
M  collaboration/work_items.json
A  formalization/NSFormalization/Section4/A04/GradientFiniteness.lean
A  research/A04/ATTEMPTS_CONTRACT.md
A  research/A04/axioms_contract.lean
A  research/A04/probes/grad_finite_probe.lean
A  verification/Bindings/EnergyHighPartial.lean
A  verification/Contracts/V1/EnergyHighPartial.lean
A  verification/Tests/EnergyHighPartial.lean
M  verification/contracts.json
```

`Contracts/V1`、`Tests`、`Bindings`、`Section4` 下全是 `A`（新增），零个 `M`。
`contracts.json` **纯追加**：

```
$ git diff 56b5757 --numstat -- verification/contracts.json     → 11  0
$ git diff 56b5757 -- verification/contracts.json | grep -c "^-[^-]"  → 0
# JSON 层比对：old count 22 → new count 23
#   added:   ['A04.energy_high_partial']
#   removed: []
#   changed existing: []          （22 条既有条目逐字段相同）
```

`research/A04/BLIND_RHIGH.md` **不在本 commit 里**（merge-base `56b5757` 上 ABSENT，
integration tip `fdd16b8` 上 PRESENT——本 lane 在 BLIND_RHIGH 合入前开的，不碰它，无冲突）。

### 禁用 token — 零命中

```
$ grep -nE "\b(sorry|admit|native_decide)\b|axiom |set_option|maxHeartbeats" <6 个新 Lean 文件>
Contracts/V1/EnergyHighPartial.lean                 hits=0
Bindings/EnergyHighPartial.lean                     hits=0
Tests/EnergyHighPartial.lean                        hits=0
Section4/A04/GradientFiniteness.lean                hits=0
research/A04/axioms_contract.lean                   hits=0
research/A04/probes/grad_finite_probe.lean          hits=0
```

---

## 2. 陈述保真 — **PASS**

### (a) 合同字段 vs tree 定理 vs spec 字段：**逐字节相同，零差异**

机器比对（`sed` 抽三段，tree 段只去掉行首 `theorem ` 与行尾 ` := by`）：

```
$ sed -n '182,192p' verification/Contracts/V1/EnergyHighPartial.lean  > /tmp/rev133/f_contract.txt
$ sed -n '424,434p' research/A04/Spec.lean                            > /tmp/rev133/f_spec.txt
$ sed -n '145,155p' formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean \
    | sed -e '1s/^theorem energyIdentityHigh/  energyIdentityHigh/' -e '$s/ := by$//' \
                                                                     > /tmp/rev133/f_tree.txt
$ diff f_contract.txt f_spec.txt   → 无输出（IDENTICAL）
$ diff f_contract.txt f_tree.txt   → 无输出（IDENTICAL）
```

任务书预期的"唯一差异是 namespace 限定符"甚至没有出现：**连限定符差异都是零**（三处都在各自
namespace 下用同一批短名）。`BLIND_RHIGH.md` §5.1 要求"照抄 tree 形"，落实到位。

### (b) 三条 `rfl` 桥：我独立重证，且是真 `Eq.refl`（非 tactic）

`/tmp/rev133/p1_bridges.lean`，由我自己写陈述、用 `Eq.refl _` term-mode 而非 `rfl` tactic，
**双向**各一条，另加一条"合同的梯度 def 真的走注册过的 `Contracts.V1.TameProduct` 对象"：

```lean
example : C.sobolevNormAt          = A04.sobolevNormAt          := Eq.refl _
example : C.gradientSobolevNormAt  = A04.gradientSobolevNormAt  := Eq.refl _
example : C.HasSmoothSobolevPath   = A04.HasSmoothSobolevPath   := Eq.refl _
example : A04.sobolevNormAt          = C.sobolevNormAt          := Eq.refl _   -- 反向
example : A04.gradientSobolevNormAt  = C.gradientSobolevNormAt  := Eq.refl _
example : A04.HasSmoothSobolevPath   = C.HasSmoothSobolevPath   := Eq.refl _
example : C.gradientSobolevNormAt
    = fun (s : ℝ) (u : SpaceTimeField) (t : ℝ) =>
        (Contracts.V1.TameProduct.gradientSobolevENorm s (fun x : Space => u (t,x))).toReal
    := Eq.refl _
```
```
$ lake env lean /tmp/rev133/p1_bridges.lean
（所有 example 静默通过；只有 #check / #print axioms 输出）
```

三个 def 的**文本**核对（`Contracts/V1/EnergyHighPartial.lean` vs tree）：

| def | tree 出处 | 差异 |
|---|---|---|
| `sobolevNormAt` | `Section4/A04/Forcing.lean:74` | 无，逐字 |
| `gradientSobolevNormAt` | `Section4/A04/LaplacianDatum.lean:86` | 仅 `TameProduct.` 限定符（tree 用 A03 的同名对象）——正是桥要守的那处 |
| `HasSmoothSobolevPath` | `Section4/A04/DerivNorm.lean:87`（＝ `Spec.lean:247`） | 无，5 行逐 token 相同 |

Bindings 里三条桥本身也是 `:= rfl`，`#print axioms` 三条都是标准三公理。

### (c) scope 串 / 模块 docstring vs `BLIND_RHIGH.md` §5.3 — 七条全覆盖

| §5.3 要求 | 合同 docstring | `contracts.json` scope |
|---|---|---|
| 1. `HasSmoothSobolevPath` 是假设不是结论；＝ A01 `sobolev_smooth`（`Spec.lean:180`, m1, L, gap）；不可由 `ClassicalSolutionR.sobolev` 导出（只给 `ContinuousOn`）；**最重要的披露** | ✅ 独立一节 "## The hypothesis `HasSmoothSobolevPath`, and why the field is CONDITIONAL"，结尾写明 "This is the single most important disclosure of the contract" | ✅ "CONDITIONAL on HasSmoothSobolevPath …, the single most important disclosure" |
| 2. `Chigh` opaque：只断言 `0 < Chigh m`，不断言 `= tame.Ctame`（binding 里作 bonus），不断言任何别的等同 | ✅ 字段 docstring "Kept **opaque** … not `Chigh = tame.Ctame` nor any other identification" | ✅ 同，并点名 bonus 名 |
| 3. `‖∇u‖_{H^m}` 是梯度张量范数，**不是** `‖u‖_{H^{m+1}}`；阶移 out of scope | ✅ "Conventions" 节 | ✅ |
| 4. 时间集 `Ioo 0 T`，`t=0` 不断言 | ✅ "the field speaks only on the open interior `Ioo 0 T`" | ✅ 并补"datum 路径在 `Ico 0 T` 上 C^∞，单侧导数可得但未断言" |
| 5. `.toReal` 约定 + 四个有限性事实（含**本 lane 新落地**的 `gradientSobolevENorm_velocity_ne_top`） | ✅ 点名 `Continuity.lean:64,73` 三槽 + `GradientFiniteness.lean` 第四槽 | ✅ 同 |
| 6. `a ∈ initialClassR` 未用、`0<ν`/`3≤m` 有余量、V1 不弱化 | ✅ 写了 | ✅ 写了 — **但引用的文件不含该记录，见 finding 1** |
| 7. 不断言 eq:highcontinuation / eq:criterion / eq:mild / `t=0` | ✅ 独立 "## Out of scope, and asserted nowhere" 节 | ✅ 末段 |

`a ∈ initialClassR` 确实未用，我在 tree 源码直接看到：
`EnergyIdentityHigh.lean:156` `intro ν a f T hν _ha hf w hpath m hm t ht`（`_ha` 下划线）。

### (d) 非空洞性 — **合同层面完整实例化，我自己建的**

`/tmp/rev133/p2_vacuity.lean`。把 `zeroSol` 按 `research/D01/REVIEW_SL8_ASSEMBLY.md` 附录 A 
**重建为 `Contracts.V1.Data.ClassicalSolutionR`**（不是 A02 那份），并用**合同自己的**
`HasSmoothSobolevPath` 给出见证，然后 discharge 合同字段：

```lean
def zeroSol (ν : ℝ) : ClassicalSolutionR ν 0 0 1 := …          -- Data 层，10 个字段
theorem zero_mem_initialClassR : (0 : SpatialField) ∈ initialClassR := …
theorem memForceR_zero : MemForceR (0 : SpaceTimeField) := …
theorem path_zero (ν : ℝ) :
    Contracts.V1.EnergyHighPartial.HasSmoothSobolevPath 1 (zeroSol ν).velocity :=
  fun m => ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const⟩
theorem rhigh_on_zeroSol : ∃ d : ℝ, HasDerivAt … ∧ … :=
  Bindings.energyHighPartial.energyIdentityHigh 1 0 0 1 one_pos
    zero_mem_initialClassR memForceR_zero (zeroSol 1) (path_zero 1) 3 le_rfl (1/2) …
theorem grad_finite_on_zeroSol : TameProduct.gradientSobolevENorm ((3:ℕ):ℝ) … ≠ ⊤ :=
  Bindings.energyHighPartial_gradientSobolevENorm_velocity_ne_top (zeroSol 1) 3 …
```
```
$ lake env lean /tmp/rev133/p2_vacuity.lean
'Rev133V.rhigh_on_zeroSol'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev133V.path_zero'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev133V.grad_finite_on_zeroSol' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

结论：整个假设包（`0<ν`、`a ∈ initialClassR`、`MemForceR f`、一个 **Data 层**
`ClassicalSolutionR`、`HasSmoothSobolevPath`、`3≤m`、`t ∈ Ioo 0 T`）**在合同词汇里可满足**。
那条"条件式"假设不是不可满足子句。（这补上了 ATTEMPTS N2 说"不放进 Tests"的那块——
128 审稿是在 formalization 词汇里做的，这里是在合同词汇里做的。）

API 是闭值、类型闭合：

```
$ #check (Bindings.energyHighPartial : Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI)
BlowupDensity.Bindings.energyHighPartial : …EnergyHighPartialAPI
$ #check @…EnergyHighPartialAPI
…EnergyHighPartialAPI : Type                       ← 带数据字段 ⇒ 绑定是 def，正确
$ #check @…EnergyHighPartialAPI.Chigh_pos
… : ∀ (self : …EnergyHighPartialAPI) (m : ℕ), 0 < self.Chigh m
```

`Chigh_pos` 不是 `0 < 0` 式空洞——我把它一路展开到 A03 的具体常数：

```lean
example (m : ℕ) : Bindings.energyHighPartial.Chigh m
    = 6 * (3 * NSFormalization.Section4.A03.scalarTameConst m) := Eq.refl _
example : Bindings.energyHighPartial.Chigh = A03.outerTameConst := Eq.refl _
```
（`A03/OuterTameProduct.lean:166` `outerTameConst k = 6 * vectorTameConst k`，
`A03/VectorTameProduct.lean:264` `vectorTameConst m = 3 * scalarTameConst m`。）

`energyHighPartial_Chigh_eq_Ctame` 我独立复证是真 `rfl`，且对手方确实是**注册过的**
`TameProductAPI.Ctame`（`Bindings/TameProduct.lean:102` `Ctame := A03.outerTameConst`）：

```lean
example : Bindings.energyHighPartial.Chigh = Bindings.tameProduct.Ctame := Eq.refl _
example : ∀ m : ℕ, 0 < Bindings.tameProduct.Ctame m := Bindings.tameProduct.Ctame_pos
```

### (e) `gradientSobolevENorm_velocity_ne_top`

```
$ #check @NSFormalization.Section4.A04.gradientSobolevENorm_velocity_ne_top
∀ {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}
  (w : A02.ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ},
  t ∈ Ioo 0 T → (A03.gradientSobolevENorm ↑m fun x => w.velocity (t, x)) ≠ ⊤
'…gradientSobolevENorm_velocity_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**是**：对古典解的速度、内点时刻、**无任何额外假设**（只有 `w`、`m`、`t ∈ Ioo 0 T`）。
合同的 `.toReal` 披露确实引用了它（模块 docstring "Conventions" 节 +
`gradientSobolevNormAt` 的 def docstring + scope 串，三处）。Binding 层的
`energyHighPartial_gradientSobolevENorm_velocity_ne_top` 把它搬到合同的
`Contracts.V1.TameProduct.gradientSobolevENorm` 上，`#check` 确认签名对齐。
参见 finding 2（`Ioo` 比同族窄）。

---

## 3. 一致性 — **PASS**

**import 政策。** 合同只有两行 import：

```
1:import Contracts.V1.Data
2:import Contracts.V1.TameProduct
```

这满足 **CLAUDE.md 的原始严格规则**，根本没用上 009 那个"+ `NavierStokes.*` + 6 个白名单模块"的
临时放宽——比现有多数合同更保守。

`open NSFormalization.Paper3 (RealVectorSobolev)` 走的是**传递 import**（`Contracts.V1.Data`
的 1-4 行直接 import 了 4 个 Paper3 模块）。`check_contracts.py:100-108` 只对
`^\s*(?:public\s+)?import\s+` 匹配出来的行跑 `contract_import_allowed`，`open` 不在管辖范围内，
所以政策接受（实测 `registered_contracts: 23, base_compatibility_checked: True`）。
而且这不是钻空子：`RealVectorSobolev` 声明在
`NSFormalization.Paper3.RealVectorPositiveDensity:15`，**该模块就在
`CONTRACT_CANONICAL_MODULES` 白名单里**——直接 import 也会过。
先例：已注册的 `Contracts/V1/TameProduct.lean:111` 用的就是同一个
`open NSFormalization.Paper3 (…)` 写法。docstring 说了名字来自 Paper3（见 finding 3）。

**命名约定 vs `EnergyAbsorptionPartial`（C01.energy_absorption_partial）——完全一致：**

| 层 | EnergyAbsorptionPartial | EnergyHighPartial |
|---|---|---|
| 合同 | `namespace BlowupDensity.Contracts.V1.EnergyAbsorptionPartial` + `structure EnergyAbsorptionPartialAPI` | `…V1.EnergyHighPartial` + `structure EnergyHighPartialAPI` |
| 绑定 | 扁平 `namespace BlowupDensity.Bindings`；`def energyAbsorptionPartial`；桥 `energyAbsorptionPartial_<x>_eq` | 同构：`def energyHighPartial`；桥 `energyHighPartial_<x>_eq` |
| 测试 | `def checkedEnergyAbsorptionPartial` + `run_cmd TestSupport.checkAxioms` | `def checkedEnergyHighPartial` + 同 |

**台账。** A04 的 `kind` 是 `specification`（与 A03、C01 同）。`check_work_queue.py:22` 只对
`kind ∈ {proof, assembly}` 强制"必须有已注册合同"，对 `specification` 无此约束——
给 specification 项挂合同是允许的，A03/C01 已有先例。`make check` 里该脚本输出
"30 work items: … consistent."。

**render 幂等。** 重跑一遍，工作区干净：

```
$ python3 experiments/tasks.py render && git status --short
（无输出 ⇒ 提交的 TASKS.md / tasks/A04.md 与新 render 一致）
```

**无重名。** 源码（排除 `.lake/`）里 `theorem gradientSobolevENorm_velocity_ne_top` 只有一处：
`Section4/A04/GradientFiniteness.lean:58`。`research/A04/probes/grad_finite_probe.lean:14` 是本
lane 的草稿副本，在 `namespace ProbeGrad` 下，不进 build（lane 惯例）。参见 finding 4。

---

## 4. ATTEMPTS 的诚实性 — **PASS**

### N1 逐字复现（而且我做得更强）

`/tmp/rev133/p3_n1.lean`。记录里的 N1 用的是 formalization 词汇，我改用**合同自己的**
`Contracts.V1.EnergyHighPartial.HasSmoothSobolevPath` 和 `Data.ClassicalSolutionR`：

```lean
theorem hssp_of_classicalSolution {ν a f T} (w : ClassicalSolutionR ν a f T) :
    Contracts.V1.EnergyHighPartial.HasSmoothSobolevPath T w.velocity := by
  intro m
  obtain ⟨G, hGc, hGd⟩ := w.sobolev m
  exact ⟨G, hGd, hGc⟩
```
```
$ lake env lean /tmp/rev133/p3_n1.lean
/tmp/rev133/p3_n1.lean:18:17: error: Application type mismatch: The argument
  hGc
has type
  ContinuousOn G (Ico 0 T)
but is expected to have type
  ContDiffOn ℝ ∞ G (Ico 0 T)
in the application
  ⟨hGd, hGc⟩
```

与 `ATTEMPTS_CONTRACT.md` 粘贴的错误文本**逐字符相同**，也与 `BLIND_RHIGH.md` §3.3
`/tmp/rev130/p4_gap.lean` 相同。缺口真实：`Data.lean:643-646` 的 `sobolev` 只给
`ContinuousOn G (Ico 0 T)`，`HasSmoothSobolevPath` 要 `ContDiffOn ℝ ∞`。

### 其余记录

* **N2**（"不在 Tests 里放零解实例化"）是设计取舍，不是编译失败，陈述诚实；它依赖的底层事实
  我已在 §2(d) **在合同词汇里独立重建**，成立。
* **"每个新模块第一次 `lake build`/`lake env lean` 就过、静默"** — 与我观察一致；lane 自己的两个
  探针我也重跑了：
  ```
  $ lake env lean ../research/A04/axioms_contract.lean
  'Bindings.energyHighPartial'                      … [propext, Classical.choice, Quot.sound]
  'Tests.checkedEnergyHighPartial'                  … [propext, Classical.choice, Quot.sound]
  'Bindings.energyHighPartial_Chigh_eq_Ctame'       … [propext, Classical.choice, Quot.sound]
  'Bindings.energyHighPartial_gradientSobolevENorm_velocity_ne_top' … 同
  $ lake env lean ../research/A04/probes/grad_finite_probe.lean
  'ProbeGrad.gradientSobolevENorm_velocity_ne_top'  … [propext, Classical.choice, Quot.sound]
  ```
* **决定 5 末尾的 defeq 断言**（"`A05.SmoothL2` 与 `A03.SmoothL2` 语法上是同一个 def"）**属实**：
  `A03/SmoothJets.lean:60-61` 与 `A05/SmoothJets.lean:44-45` 都是
  `ContDiff ℝ ∞ w ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n w) 2 volume`。
* 唯一的记录缺口是 finding 1。

---

## 5. Findings

### Finding 1 — LOW，**建议合入前修**（改 research 文件，不动合同）：引用悬空

合同 docstring 与 `contracts.json` 的 scope 串都写：

> `0 < ν`, `a ∈ initialClassR` and `3 ≤ m` are stated as the manuscript does; the proof has
> slack (`0 ≤ ν`, `2 ≤ m`, and `a ∈ initialClassR` unused), **recorded in
> `research/A04/ATTEMPTS_CONTRACT.md`**, not weakened in V1.

但该文件里没有这条记录：

```
$ grep -n "0 ≤ ν\|2 ≤ m\|slack\|unused" research/A04/ATTEMPTS_CONTRACT.md
（无输出，RC=1）
```

实际记录在 lane 128 的 `research/A04/ATTEMPTS_ENERGY_HIGH.md:43,47`：

```
43:| `0 < ν` | **yes** (not tight) | only as `le_of_lt hν` → `inner_energy_Rhigh` 的 `hν : 0 ≤ ν`；
                                     mathematically `0 ≤ ν` suffices, kept `0 < ν` for spec fidelity |
47:| `3 ≤ m` | **yes** (not tight) | only via `have hm2 : 2 ≤ m := by omega`；
                                     this route needs only `m ≥ 2`, kept `3 ≤ m` per manuscript `:129` |
```

事实本身为真（我在 tree 源码直接确认 `_ha` 未用），只是指针差一个文件。**影响**：
`Contracts/V1` 合入后冻结，这行引用以后改不动了。**修法**（零风险）：把上面两行抄进
`research/A04/ATTEMPTS_CONTRACT.md`（非生成、非冻结文件），引用即成立，合同与 `contracts.json`
一个字都不用动。

### Finding 2 — LOW（可留作 follow-up）：`GradientFiniteness` 的 `Ioo` 比它自称加入的同族窄

新引理用 `ht : t ∈ Ioo (0:ℝ) T`，但模块 docstring 自称是
"The fourth member of the finiteness family `Section4/A04/Continuity.lean`"，而该族的
`sobolevENorm_velocity_ne_top`（`Continuity.lean:64`）用的是 `ht : t ∈ Ico (0:ℝ) T`。
而且本引理证明的**第一行**就是把 `Ioo` 弱化成 `Ico`：
`have ht' : t ∈ Ico (0:ℝ) T := ⟨le_of_lt ht.1, ht.2⟩`——`Ico` 版是白送的。实证
（`/tmp/rev133/p4_ico.lean`，证明就是原证明删掉那一行）：

```lean
theorem gradientSobolevENorm_velocity_ne_top_ico … (ht : t ∈ Ico (0:ℝ) T) :
    gradientSobolevENorm (m:ℝ) (fun x => w.velocity (t,x)) ≠ ⊤ := …
example … (ht : t ∈ Ioo (0:ℝ) T) : … :=
  gradientSobolevENorm_velocity_ne_top_ico w m (Ioo_subset_Ico_self ht)
```
```
$ lake env lean /tmp/rev133/p4_ico.lean
'Rev133I.gradientSobolevENorm_velocity_ne_top_ico' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

**不影响合同**（字段本来就只量化 `Ioo 0 T`，binding 的 bonus 也只用到 `Ioo`）。代价是将来要在
`t = 0` 用它的消费者（比如 G2 的端点处理）得重证一遍。合入前改或另开 lane 都行。

### Finding 3 — INFO：`RealVectorSobolev` 的出处只写到 namespace 级

docstring 两处写 "`RealVectorSobolev` is Paper3's three-vector carrier" / "is Paper3's"，
没点名声明模块 `NSFormalization.Paper3.RealVectorPositiveDensity:15`（该模块正在
`CONTRACT_CANONICAL_MODULES` 白名单上，直接 import 也合法）。对比 `Data.lean:66` 自己的出处表
是点名到模块的。`ATTEMPTS_CONTRACT.md` 决定 4 把整件事解释清楚了，所以只是 INFO，不要求动作。

### Finding 4 — INFO：tree 里有一处同形的内联证明可供将来吸收

`D01/Pressure.lean:271-275` 有个局部 `have hgrad : ∀ s : ℝ, A03.gradientSobolevENorm s us ≠ ⊤`，
骨架与新引理完全一样（`columnsSobolevENorm_le_sum` + `ENNReal.sum_ne_top`），但对象是一般的
`SmoothSquareIntegrableJets us`，不是古典解速度切片。不是重名、不是重复声明，不要求本 lane 处理；
将来若把新引理抽成"对任意 `SmoothL2` 场"的版本，这处可以复用。

---

## 6. 跑过的全部命令

```
. scripts/lean-env.sh                                                    # Lean 4.34.0-rc2
cd verification
LEAN_NUM_THREADS=6 lake build Tests.EnergyHighPartial                    # EXIT=0, 10023 jobs,
                                                                         #   "checked; standard logical axioms only"
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.GradientFiniteness  # EXIT=0, 9884 jobs
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A04/GradientFiniteness.lean
                                                                         # EXIT=0, 静默
make check                                                               # EXIT=0（13 policy tests OK；30 work items consistent）
make test                                                                # EXIT=0，23 条 checked
make test-mutations                                                      # EXIT=0，4 条变异结论符合预期
python3 experiments/check_contracts.py --base-ref origin/erenup/integration
                                                                         # registered_contracts: 23
                                                                         # base_compatibility_checked: True
python3 experiments/tasks.py render && git status --short                # 无输出（幂等）
git diff 56b5757 --name-status / --numstat                               # 见 §1
lake env lean /tmp/rev133/p1_bridges.lean    # EXIT=0，7 条 Eq.refl 桥 + 4 条常数恒等全过
lake env lean /tmp/rev133/p2_vacuity.lean    # EXIT=0，合同层零解实例化，3 个定理标准三公理
lake env lean /tmp/rev133/p3_n1.lean         # EXIT=1（预期失败），N1 错误文本逐字符复现
lake env lean /tmp/rev133/p4_ico.lean        # EXIT=0，Ico 推广是白送的（finding 2）
lake env lean ../research/A04/axioms_contract.lean          # EXIT=0，4 条标准三公理
lake env lean ../research/A04/probes/grad_finite_probe.lean # EXIT=0，标准三公理
diff /tmp/rev133/f_contract.txt /tmp/rev133/f_spec.txt      # 无输出：逐字节相同
diff /tmp/rev133/f_contract.txt /tmp/rev133/f_tree.txt      # 无输出：逐字节相同
grep -nE "sorry|admit|native_decide|axiom |set_option|maxHeartbeats" <6 个新 Lean 文件>  # 0 命中
```

所有成功的探针只依赖 `propext` / `Classical.choice` / `Quot.sound`。
