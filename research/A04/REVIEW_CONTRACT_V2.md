# 审稿 — lane 141（A04 合同 **V2**，`A04.energy_high_partial_v2`）

被审对象：`erenup/141-A04-energy-high-v2`，相对 `origin/erenup/integration` 的 merge-base
（`3b10c06`）**一个 commit**（`cd4b6aa`），11 个文件、701 插入 / 3 删除，无文件删除：

```
verification/Contracts/V2/EnergyHighPartial.lean   (+268)   新
verification/Bindings/EnergyHighPartialV2.lean     (+91)    新
verification/Tests/EnergyHighPartialV2.lean        (+80)    新
verification/contracts.json                        (+11/-0) 纯追加
research/A04/ATTEMPTS_CONTRACT_V2.md               (+131)   新
research/A04/axioms_contract_v2.lean               (+87)    新
research/A04/probes/v2_no_transport.lean           (+20)    新
research/A04/probes/v2_wrong_cgron.lean            (+9)     新
collaboration/work_items.json                      (+2/-1)  台账
collaboration/TASKS.md, collaboration/tasks/A04.md (+1/-1)  生成物
```

**结论：ACCEPT-WITH-NOTES。** 两个新字段与 `research/A04/Spec.lean` 草稿字段、与树里已证定理
**三方 token 级完全相同**；`MemL1Hm` 逐字重述且第四条 `rfl` 桥为真；`Cgron` 在合同里确实不透明；
十条披露 + 孤儿披露逐条落实；门禁全绿、24 个合同标准三公理；非空洞性我在**合同词汇**里独立复现。
四条 note 全部是**记录性**的（引用区间不对齐、探针少一个 import、两处文字数字），零阻塞、不改 Lean。

审稿环境：worktree 内 `. scripts/lean-env.sh`，`lake` 一律从 `verification/` 跑，`LEAN_NUM_THREADS=6`；
探针在 `/tmp/rev141/`（易失，报错原文已抄进本文件）。

---

## 1. 编译 / 政策 / 卫生 — **PASS**

```
$ cd verification && LEAN_NUM_THREADS=6 lake build Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2:
        checked; standard logical axioms only
Build completed successfully (10028 jobs).                       # EXIT=0

$ make check                                                     # EXIT=0
  check_contracts (architecture) OK；test_contract_policy: Ran 13 tests OK；
  check_work_queue: 30 work items: ownership, contract registration and task cards consistent.

$ make test                                                      # EXIT=0
  24 个合同，全部 "checked; standard logical axioms only"（grep -c = 24），
  其中 checkedEnergyHighPartial（V1，未动）与 checkedEnergyHighPartialV2 并列出现。

$ make test-mutations                                            # EXIT=0
  implementation_refactor: accepted
  admitted_proof: rejected as required
  extra_axiom: rejected as required
  weakened_hypothesis: rejected as required
  Mutation suite passed.

$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration     # EXIT=0
  {"registered_contracts": 24, ..., "base_compatibility_checked": true, ...}
```

**冻结面**：`git diff 3b10c06 --name-status` 里**没有** `Contracts/V1/EnergyHighPartial.lean`、
`Bindings/EnergyHighPartial.lean`、`Tests/EnergyHighPartial.lean`，也没有任何 `Contracts/V1/*`、
`Tests/*` 的修改；新增文件全是 `A`。

**`contracts.json` 纯追加**，逐条核过（不是只看 diff 长度）：

```
$ git diff 3b10c06 -- verification/contracts.json | grep '^-' | grep -v '^---'
（空）

$ python3  # 结构化比对
base ids: 23   head ids: 24
added:   ['A04.energy_high_partial_v2']
removed: []
changed existing entries: []
top-level keys base: ['contracts','schema_version'] head: 同
```

**`ensure_ascii` 陷阱未复发**：HEAD 的 `contracts.json` 里 `\uXXXX` escape **零命中**
（`grep -c '\\u'` → 0，base 亦 0），已有条目里的 `ν` / `R³` / `↪` / `Ḣ` 仍是原始 UTF-8 字节。

**卫生 grep**（六个新 Lean 文件）：

```
$ grep -nE 'sorry|admit|axiom|native_decide|set_option|maxHeartbeats' \
    verification/Contracts/V2/EnergyHighPartial.lean \
    verification/Bindings/EnergyHighPartialV2.lean \
    verification/Tests/EnergyHighPartialV2.lean \
    research/A04/axioms_contract_v2.lean research/A04/probes/v2_*.lean
research/A04/axioms_contract_v2.lean:10,33-36    （docstring 的命令行 + 四条 #print axioms）
verification/Contracts/V2/EnergyHighPartial.lean:141   （docstring "standard three axioms" 字样）
```

即：无 `sorry` / `admit` / `axiom` 声明 / `native_decide` / `set_option` / `maxHeartbeats`。

**公理审计**（lane 自带的 conformance 文件，我复跑）：

```
$ cd verification && lake env lean ../research/A04/axioms_contract_v2.lean       # EXIT=0
'BlowupDensity.Bindings.energyHighPartialV2'             depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.energyHighPartialV2_memL1Hm_eq'  depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.energyHighPartialV2_Cgron_eq'    depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.energyHighPartial_of_v2'         depends on axioms: [propext, Classical.choice, Quot.sound]
```
文件里三个 conformance `example`（V2 API 被绑定见证、两个字段在**合同词汇**里被见证 discharge）
与第四条桥的 `example` 同时 elaborate 通过，无额外输出。

---

## 2. 陈述保真 — **PASS**

### (a) 两个新字段：spec / 合同 / 树 三方 token 级**完全相同**

把三处的字段类型各自 tokenize（去掉字段名与 `:= by`）后 `difflib` 比对。**无需任何名字替换**——
三边用的标识符拼写本来就一致（`sobolevNormAt`、`Cgron`、`MemForceR`、`HasSmoothSobolevPath`、
`initialClassR`、`ClassicalSolutionR` 都是 `open` 之后的裸名）。

| 字段 | spec | 合同 | 树 | 结果 |
|---|---|---|---|---|
| `regularizedNormDerivative` | `Spec.lean:459-470` | `Contracts/V2/EnergyHighPartial.lean:221-232` | `A04/HighContinuation.lean:183-194` | 138 / 138 / 138 tokens，**IDENTICAL** |
| `highContinuationIntegral` | `Spec.lean:494-510` | `:250-266` | `A04/HighContinuationIntegral.lean:85-101` | 163 / 163 / 163 tokens，**IDENTICAL** |
| `Cgron` | `Spec.lean:354` | `:199` | —（`A04.Cgron` 是 `def`，合同不重述） | 7 / 7，**IDENTICAL** |
| `Cgron_pos` | `Spec.lean:356` | `:204` | — | 21 / 21，**IDENTICAL** |

（G2b 的 163 token 与 138 审稿独立测得的 163 一致，两次比对互为旁证。）

字段顺序与 `extends` 的结构性：`EnergyHighPartialV2API extends
BlowupDensity.Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI`，V1 字段一个不改、不删、不改名，
且由 `energyHighPartial_of_v2` 的 `rfl` 把这件事**钉死**（见 (c)）。

### (b) `MemL1Hm` 逐字重述 + 第四条桥真的是 `rfl` — **PASS**

三处 25 token 全同：

```
research/A04/Spec.lean:268                       def MemL1Hm (f : SpaceTimeField) : Prop :=
                                                   ∀ m : ℕ, forceSobolevENormL1 (m : ℝ) f ≠ ⊤
Section4/A04/Forcing.lean:110                    同上（逐 token）
Contracts/V2/EnergyHighPartial.lean:168          同上（逐 token）
```

桥与另两条 `rfl` 事实，我**不用 lane 的定理名、从零重证**（`/tmp/rev141/p_bridge.lean`）：

```lean
example : Contracts.V2.EnergyHighPartial.MemL1Hm = NSFormalization.Section4.A04.MemL1Hm := rfl
example : Bindings.energyHighPartialV2.toEnergyHighPartialAPI = Bindings.energyHighPartial := rfl
example (m : ℕ) (ν : ℝ) : Bindings.energyHighPartialV2.Cgron m ν
    = NSFormalization.Section4.A04.Chigh m ^ 2 / (4 * ν) := rfl
```
```
$ lake env lean /tmp/rev141/p_bridge.lean        # EXIT=0，无输出
```

**桥不是装饰**：非空洞性探针里 `memL1Hm_zero : Contracts.V2…MemL1Hm 0` 是直接用树里的
`A04.memL1Hm_of_memForceR memForceR_zero` 填的，跨 defeq 无 cast 通过——同时实证了披露 8
（`MemL1Hm` 可由 `MemForceR` 推出）。

`Contracts/` 下 `MemL1Hm` 的 `def` **只有一份**（`grep -rn 'MemL1Hm' verification/Contracts/`：
V2/EnergyHighPartial.lean 的 10 处命中里只有 `:168` 是定义，其余全是 docstring）。

### (c) `Cgron` 不透明 / `Cgron_pos` 为真 / 两个负例复现 — **PASS**

**不透明是被检验过的，不是读代码猜的**（`/tmp/rev141/p_opaque.lean`）：对一个**任意**的 API 实例
去证值等式，`rfl` 失败——说明合同确实没有钉住值。

```
$ lake env lean /tmp/rev141/p_opaque.lean        # EXIT=1
p_opaque.lean:7:49: error: Type mismatch
  rfl
has type
  ?m.24 = ?m.24
but is expected to have type
  api.Cgron m ν = api.Chigh m ^ 2 / (4 * ν)
```

结构体里 `Cgron : ℕ → ℝ → ℝ` + `Cgron_pos : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < Cgron m ν` 是仅有的两条，
没有第三条把值写进去。值只在 binding 的 bonus 里（上面 `p_bridge.lean` 第三个 `example` 已复证）。

**负例 1，`v2_no_transport`（去掉 `uniqueness_toA02`）**：

```
$ cd verification && lake env lean ../research/A04/probes/v2_no_transport.lean      # EXIT=1
v2_no_transport.lean:16:8: error: Application type mismatch: The argument
  w
has type
  ClassicalSolutionR ν a f T
but is expected to have type
  NSFormalization.Section4.A02.ClassicalSolutionR ν a f T
in the application
  NSFormalization.Section4.A04.regularizedNormDerivative ν a f T hν ha hf w
v2_no_transport.lean:18:6: error(lean.unknownIdentifier): Unknown identifier
  `NSFormalization.Section4.A04.highContinuationIntegral`
```
第一条正是要的；第二条是探针少 import 的噪声（**发现 2**）。

**负例 2，`v2_wrong_cgron`（`/(2ν)` 而不是 `/(4ν)`）**：

```
$ cd verification && lake env lean ../research/A04/probes/v2_wrong_cgron.lean       # EXIT=1
v2_wrong_cgron.lean:6:0: error: Not a definitional equality: the left-hand side
  energyHighPartialV2.Cgron m ν
is not definitionally equal to the right-hand side
  NSFormalization.Section4.A04.Chigh m ^ 2 / (2 * ν)
v2_wrong_cgron.lean:8:2: error: Type mismatch
  rfl
has type
  ?m.24 = ?m.24
but is expected to have type
  energyHighPartialV2.Cgron m ν = NSFormalization.Section4.A04.Chigh m ^ 2 / (2 * ν)
```

**V1 投影守卫**：`energyHighPartial_of_v2 : …toEnergyHighPartialAPI = energyHighPartial := rfl`。
这条比树里 A02 的同名物**强**（ATTEMPTS 决策 5 的自述属实，我核了）：
`Bindings/MaximalPartialV2.lean:124` 是 `theorem maximalPartial_of_v2 : …MaximalPartialAPI :=
maximalPartialV2.toMaximalPartialAPI`——只是"可居留"，不是"等于那个冻结见证"。141 给的是等式。

### (d) 十条披露 + 孤儿披露 — **逐条覆盖，PASS**

`REVIEW_G2B.md` §5.3（1–10）与 §5.4（孤儿）要求的，全部落在
`Contracts/V2/EnergyHighPartial.lean` 的模块 docstring 与 `contracts.json` 的 scope 串里：

| # | `REVIEW_G2B.md` 要求 | 合同 docstring | `contracts.json` scope |
|---|---|---|---|
| 1 | `Cgron` 不透明，只断言 `0 < Cgron m ν`，值只在 binding | ✅ `:77-80` + 字段 docstring `:195-198` | ✅ "(1) Cgron OPAQUE …" |
| 2 | `ν = 0` 是 junk（`Cgron m 0 = 0`），`0 < ν` 不可减弱为 `0 ≤ ν` | ✅ `:81-85`（点名 `p_nu0.lean` / 135 审稿 `p7_dup.lean`） | ✅ "(2) At nu = 0 … stronger and false" |
| 3 | 积分形（`ζ↓0` 之后），不是微分形；理由（零点不必可导 / Grönwall 唯一吃的形状） | ✅ `:86-90` | ✅ "(3) … not a differential one" |
| 4 | `IntervalIntegrable` 是**被断言**的，不是被假设；否则积分 junk `0` | ✅ `:91-96`（点名 N1 `Continuity.lean:132`） | ✅ "(4) … ASSERTED not assumed" |
| 5 | `.toReal` 只覆盖 velocity / force 槽，**不**照抄 V1 的梯度槽那句 | ✅ `:97-104`，明写 "deliberately not repeated" | ✅ "(5) … NO gradient norm appears … deliberately not repeated" |
| 6 | 端点 `0 ≤ t₀ ≤ t < T`，`t₀ = 0` **在内**，靠连续性而非 `HasSmoothSobolevPath` | ✅ `:105-111`，并写了 G2 只在 `Ioo 0 T` | ✅ "(6) endpoints … t0 = 0 INCLUDED …" |
| 7 | 仍**条件于** `HasSmoothSobolevPath`（A01 m1，gap），最重要的一条，不得弱化 | ✅ `:112-117`，"single most important disclosure … does not weaken it" | ✅ "(7) STILL CONDITIONAL …" |
| 8 | `MemL1Hm` 冗余、可由 `MemForceR` 经 `memL1Hm_of_memForceR`（F1a）推出 | ✅ `:118-123` | ✅ "(8) MemL1Hm f is redundant …" |
| 9 | `a ∈ initialClassR` 是 slack（继承 V1 披露） | ✅ `:124-126` | ✅ "(9) a in initialClassR is slack …" |
| 10 | eq:criterion / Grönwall 推论 / uniform restart / eq:mild / first-crossing 全部 out of scope | ✅ `:127-131` | ✅ "(10) OUT OF SCOPE …" |
| §5.4 | 两字段**并列**、G2b **不经过** G2、G2 目前零证明消费者 | ✅ `:133-142` "**Parallel, not sequential**" 独立段 | ✅ "PARALLEL not sequential …" |

**引用行号我全查了**（LESSONS「论文/源码行号会代代相传」），**11 处全部准确**：

```
Continuity.lean:64    theorem sobolevENorm_velocity_ne_top …
Continuity.lean:73    theorem sobolevENorm_force_ne_top …
Continuity.lean:132   theorem intervalIntegrable_highContinuationIntegrand
Forcing.lean:110      def MemL1Hm (f : SpaceTimeField) : Prop :=
Forcing.lean:140      theorem memL1Hm_of_memForceR … : MemL1Hm f := by
Data.lean:231         abbrev forceSobolevENormL1 (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
A01/Spec.lean:180     sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
HighContinuation.lean:183   theorem regularizedNormDerivative :
A04/Spec.lean:354/356/268   Cgron / Cgron_pos / MemL1Hm
```

**孤儿状态仍然成立**（复核 §5.4 的前提）：`formalization/` 里 `regularizedNormDerivative` 只有
定义处（`HighContinuation.lean:183`）与两处 docstring 提及（同文件、`DerivNorm.lean`），
**零个证明消费者**。本 lane 之后它在**合同层**有了消费者（`Bindings/EnergyHighPartialV2.lean` 绑定它），
但 docstring 说的是 "zero proof consumers **in the tree**"，口径正确（见发现 4 的读法提示）。

### (e) 非空洞性 — **PASS**（我在合同词汇里独立重建，不是引用 138 的 A02 层结果）

API 是闭值、类型闭合：

```
$ #check @BlowupDensity.Contracts.V2.EnergyHighPartial.EnergyHighPartialV2API
BlowupDensity.Contracts.V2.EnergyHighPartial.EnergyHighPartialV2API : Type      ← 带数据字段 ⇒ 绑定是 def，正确
$ #check (BlowupDensity.Bindings.energyHighPartialV2 : …EnergyHighPartialV2API)
BlowupDensity.Bindings.energyHighPartialV2 : …EnergyHighPartialV2API
```

`/tmp/rev141/p_vacuity.lean`：按 `research/A04/REVIEW_CONTRACT.md` §(d)（133 审稿）把 `zeroSol`
重建为 **`Contracts.V1.Data.ClassicalSolutionR`**（10 个字段，不是 A02 那份），
用**合同自己的** `HasSmoothSobolevPath` 给见证，然后 discharge **V2 的两个字段**：

```lean
def zeroSol (ν : ℝ) : ClassicalSolutionR ν 0 0 1 where …            -- Data 层
theorem zero_mem_initialClassR : (0 : SpatialField) ∈ initialClassR := …
theorem memForceR_zero : MemForceR (0 : SpaceTimeField) := …
theorem path_zero (ν : ℝ) : HasSmoothSobolevPath 1 (zeroSol ν).velocity :=
  fun m => ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const⟩
theorem memL1Hm_zero : MemL1Hm (0 : SpaceTimeField) :=               -- 跨第四条桥，无 cast
  NSFormalization.Section4.A04.memL1Hm_of_memForceR memForceR_zero

theorem g2b_on_zeroSol : IntervalIntegrable … volume 0 (1/2) ∧ … :=  -- t₀ = 0 端点真的取到
  Bindings.energyHighPartialV2.highContinuationIntegral 1 0 0 1 one_pos
    zero_mem_initialClassR memForceR_zero memL1Hm_zero (zeroSol 1) (path_zero 1) 3 le_rfl
    0 (1/2) le_rfl (by norm_num) (by norm_num)

theorem g2_on_zeroSol : ∃ d : ℝ, HasDerivAt … d (1/2) ∧ … :=         -- ζ = 1/3
  Bindings.energyHighPartialV2.regularizedNormDerivative 1 0 0 1 one_pos
    zero_mem_initialClassR memForceR_zero (zeroSol 1) (path_zero 1) 3 le_rfl (1/2)
    (by constructor <;> norm_num) (1/3) (by norm_num)
```
```
$ lake env lean /tmp/rev141/p_vacuity.lean      # EXIT=0（只有两条 unusedVariables linter warning）
'Rev141V.g2b_on_zeroSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev141V.g2_on_zeroSol'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev141V.memL1Hm_zero'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

即：整包假设（`0<ν`、`a ∈ initialClassR`、`MemForceR`、**Data 层** `ClassicalSolutionR`、
`HasSmoothSobolevPath`、`MemL1Hm`、`3≤m`、`0 ≤ t₀ ≤ t < T` 含 `t₀ = 0`、`ζ > 0`）
在**合同词汇里可满足**，那条"条件式"假设不是不可满足子句。
零解上两边退化成 `0 ≤ 0 + 0`，所以这只证非空洞、不证不平凡；不平凡性 138 审稿已用
`shape_not_tautology` 单独做过（结论形状不是恒真式），本 lane 未改形状，不重做。

---

## 3. 与树的一致性 — **PASS**

* **import 政策**：`Contracts/V2/EnergyHighPartial.lean` 只有一行 `import Contracts.V1.EnergyHighPartial`，
  自动满足 `check_contracts.py` 的 `Mathlib`/`Lean`/`Init`/`Contracts.*` 规则，**不碰 009 的白名单放宽**。
  `test_contract_policy.py` 13 tests OK，`post_lean.py` 钩子口径同。
* **与其他 V2 的约定一致**：命名 `*V2API extends *API` / `Bindings/*V2.lean` / `Tests/*V2.lean` /
  `checked*V2` / `*_of_v2`，与 `Contracts/V2/{MaximalPartial,InsertionLifespan,HomogeneousPartial}.lean`
  同型；`open` 块的写法（`open Set MeasureTheory` / `open NavierStokes.ProblemStatement` /
  `open BlowupDensity.Contracts.V1.Data` / `open scoped ENNReal`）与 `MaximalPartial.lean:83-86` 逐行同构。
  `contracts.json` 里七条 v2/v3 条目的五元组（specification / binding_module / test_module / declaration）
  命名风格一致。
* **`work_items.json`** 只改 A04 的 `contracts` 数组（`+"A04.energy_high_partial_v2"`），
  `state`/`owner`/`deliverable` 不动；`check_work_queue.py` → `30 work items: … consistent.`
* **`tasks.py render` 幂等**：在 lane 的 HEAD 上重跑 `python3 experiments/tasks.py render`，
  `git status --short` **为空**，即 `TASKS.md` / `tasks/A04.md` 的那两行改动正是 render 的产物。
* **Tests 的 `warningAsError`**：`Tests/EnergyHighPartialV2.lean` 只 import
  `Contracts.V2.*` / `Bindings.*` / `TestSupport.Axioms`，不直接碰 `Formal.*`；`lake build` 通过即证。
* **`Contracts/` 下无第二份 `MemL1Hm`**（见 (b)）。

---

## 4. ATTEMPTS 的诚实度 — **三个负例两个半复现，一个数字有出入**

### N1（`uniqueness_toA02` 承重）— **真**，且 ATTEMPTS **自己披露了**探针的噪声
上面 (c) 的原文。ATTEMPTS `:88-90` 主动写了「同一探针还报 `Unknown identifier …
highContinuationIntegral`，因为它只 import 了 `HighContinuation`——是最小探针的 artefact，不是要点」。
这条自我披露属实、值得表扬。但探针因此**只测了一个字段**，见发现 2。

### N2（Young 常数是 `4ν` 不是 `2ν`）— **真**
上面 (c) 的原文，两条 error 与 ATTEMPTS `:98-102` 抄录的一致。

### N3（`ensure_ascii` 陷阱）— **实质为真，数字略有出入**
我用 lane 的 HEAD `contracts.json` 按默认 `ensure_ascii=True` 重灌，对 merge-base 取 diff：

```
$ json.dump(d, fh, indent=2)            → 1 file changed, 19 insertions(+),  8 deletions(-)
$ json.dump(d, fh, indent=2); fh.write('\n')
                                       → 1 file changed, 18 insertions(+),  7 deletions(-)
$ 被破坏的 escape（抽样）：² ³ · ¹ é ε θ ν
$ 被重写的冻结 scope（抽样）：I01.packet / I02.correction / I02.correction_v2 / A05.gradient_l6
```

ATTEMPTS 记的是「20 插入 / 8 删除」，最接近的复现是 **19 / 8**。差 1 行，实质（冻结 UTF-8 scope
被静默改写、`check_contracts.py` 不会报）**完全复现**。见发现 3。
（顺带确认 ATTEMPTS 的「`check_contracts.py` 只比 `version`/`specification`/`test_module`/
`declaration`/`enabled`，不比 scope 字节」这一句属实——我的 `--base-ref` 跑在破坏版上也会过。）

---

## 5. 发现

### 发现 1（低，记录）— `Spec.lean` 引用区间两个字段**不同口径**

- `regularizedNormDerivative` 引 `Spec.lean:459-470` = **字段体**（459 是 `regularizedNormDerivative :`，
  470 是最后一行），精确。
- `highContinuationIntegral` 引 `Spec.lean:471-494` = **docstring（471-493）+ 字段名那一行（494）**；
  字段体其实是 **494-510**。

两处不对齐。出现在 `Contracts/V2/EnergyHighPartial.lean:45`、`:235`、`contracts.json` scope、
`research/A04/axioms_contract_v2.lean:20,59`。建议统一成字段体
（`Spec.lean:494-510`）或统一成「docstring+体」（`:436-470` / `:471-510`）。
**不阻塞**、不影响 Lean；但按 LESSONS「行号会代代相传」，下一条 lane（V3 的 `eq:criterion` /
`higherOrderBound`）会照抄这个口径。

### 发现 2（低，记录 + 探针质量）— `v2_no_transport.lean` 只测了两个字段中的一个

探针缺 `import NSFormalization.Section4.A04.HighContinuationIntegral`，所以
`highContinuationIntegral` 那半边报的是 `Unknown identifier`，**没有**验证它的 transport 承重。
ATTEMPTS 已披露这是 artefact（诚实度合格），但负例本身弱了一半。我补了
`/tmp/rev141/p_no_transport_fixed.lean`（加上那一行 import，两个字段都去掉 `uniqueness_toA02`），
**两条都是真的 transport 失败**：

```
$ lake env lean /tmp/rev141/p_no_transport_fixed.lean       # EXIT=1
p_no_transport_fixed.lean:18:8: error: Application type mismatch: The argument
  w
has type
  ClassicalSolutionR ν a f T
but is expected to have type
  NSFormalization.Section4.A02.ClassicalSolutionR ν a f T
in the application
  NSFormalization.Section4.A04.regularizedNormDerivative ν a f T hν ha hf w
p_no_transport_fixed.lean:21:8: error: Application type mismatch: The argument
  w
has type
  ClassicalSolutionR ν a f T
but is expected to have type
  NSFormalization.Section4.A02.ClassicalSolutionR ν a f T
in the application
  NSFormalization.Section4.A04.highContinuationIntegral ν a f T hν ha hf hf1 w
```

建议（可合入后做，或 lead 顺手改）：往 `research/A04/probes/v2_no_transport.lean` 补那一行 import，
并把 ATTEMPTS `:88-90` 的 artefact 说明换成「两个字段的 transport 都被验证承重」。
**不阻塞**——结论没变，只是证据从一半补到全部。

### 发现 3（低，记录）— ATTEMPTS N3 的 diff 数字对不上（20/8 vs 19/8）

见第 4 节。建议把 `ATTEMPTS_CONTRACT_V2.md:110-114` 的「20-insertion / 8-deletion」改成
「19 insertions / 8 deletions（`json.dump(indent=2)` 不补末尾换行；补换行则 18/7）」，
或者干脆写「约 19 插入 / 8 删除，实质是 8 条冻结 scope 被 `\uXXXX` 重写」。
**顺带支持 ATTEMPTS 的建议**：这条值得进 `logs/LESSONS.md`（"Python 改 JSON 登记表必须
`ensure_ascii=False`"），因为 `check_contracts.py` 不比 scope 字节、CI 不会拦。

### 发现 4（很低，措辞）— 两处小文字

1. `research/A04/axioms_contract_v2.lean:13` 写「the **four** `rfl` facts」，随后只列三条
   （`MemL1Hm` 桥、`Cgron` bonus、V1 投影守卫）。应为 "three"（"four" 是下面四条
   `#print axioms` 的条数，把两个数混了）。
2. 合同 docstring `:138` 的「zero proof consumers **in the tree**」在本 lane 之后需按
   "tree = `formalization/`" 读：合同层的 `Bindings/EnergyHighPartialV2.lean` 现在**确实**消费它
   （这正是注册的意思）。措辞本身没错，只是提醒下一位读者不要据此以为它"完全没人用"。

---

## 6. 跑过的命令与结果（汇总）

```
cd verification && LEAN_NUM_THREADS=6 lake build Tests.EnergyHighPartialV2   EXIT=0（10028 jobs，checkAxioms 标准三公理）
make check                                                                   EXIT=0（architecture + 13 policy tests + work queue）
make test                                                                    EXIT=0，24/24 "standard logical axioms only"
make test-mutations                                                          EXIT=0（4 个变异按预期 accept/reject）
python3 experiments/check_contracts.py --base-ref origin/erenup/integration  EXIT=0，registered_contracts=24，base_compatibility_checked=true
python3 experiments/tasks.py render                                          EXIT=0，之后 git status 为空（幂等）
python3 experiments/check_work_queue.py                                      EXIT=0，30 work items consistent
git diff 3b10c06 --name-status                                               V1 合同/绑定/Tests 零改动，8 个新文件 + 3 个台账/生成物
git diff 3b10c06 -- verification/contracts.json | grep '^-'                  空（纯追加）；结构化比对 23→24，已有条目 0 改动
grep -c '\\u' verification/contracts.json                                     0（ensure_ascii 陷阱未复发）
grep -nE 'sorry|admit|axiom|native_decide|set_option|maxHeartbeats' 六个新文件  仅 docstring 与 #print axioms 命中
python3 (difflib) spec vs contract vs tree                                    G2 138/138/138、G2b 163/163/163、MemL1Hm 25/25/25、
                                                                             Cgron 7/7、Cgron_pos 21/21 — 全部 IDENTICAL
cd verification && lake env lean ../research/A04/axioms_contract_v2.lean      EXIT=0，四条标准三公理 + 四个 example 通过
cd verification && lake env lean ../research/A04/probes/v2_no_transport.lean  EXIT=1 ✔ 复现（含一条 import artefact，发现 2）
cd verification && lake env lean ../research/A04/probes/v2_wrong_cgron.lean   EXIT=1 ✔ 复现
/tmp/rev141/p_opaque.lean      (任意 api 的 Cgron 值等式)                     EXIT=1 ✔ Cgron 在合同里确实不透明
/tmp/rev141/p_bridge.lean      (三条 rfl 独立重证)                            EXIT=0 ✔
/tmp/rev141/p_vacuity.lean     (Data 层 zeroSol，两个字段实例化 + t₀=0 端点)   EXIT=0，标准三公理 ✔ 非空洞
/tmp/rev141/p_no_transport_fixed.lean (补 import 后两字段 transport 都承重)   EXIT=1 ✔（发现 2 的补强）
python3 (ensure_ascii 重灌复现)                                              19/8（无末尾换行）或 18/7（有），ATTEMPTS 记 20/8（发现 3）
git status --short                                                           空（worktree 干净，探针全在 /tmp）
```

---

## 7. 裁决

**ACCEPT-WITH-NOTES.** 可以合入 `erenup/integration`，**四条发现全部不阻塞、全部是 md/探针层面的记录质量**，
不需要动任何 Lean 陈述。

合入前（可选，都是 lead 顺手就能改的 md/一行 import）：

* **发现 1**：统一 `Spec.lean` 引用口径（建议 `highContinuationIntegral` 改引 `:494-510`）。
  影响四个文件的注释与一条 scope 串。
* **发现 2**：`research/A04/probes/v2_no_transport.lean` 补
  `import NSFormalization.Section4.A04.HighContinuationIntegral`，ATTEMPTS `:88-90` 相应改写。
* **发现 3**：ATTEMPTS `:110-114` 的 diff 数字改成 19/8（或写"约"）。
* **发现 4**：`axioms_contract_v2.lean:13` 的 "four" → "three"。

合入后（不阻塞，记到 MAINT）：

* `REVIEW_G2B.md` 发现 6 那条仍未做：`zeroSol` 到今天已经是**第六次**手抄（133、135、138、141 各一次，
  加上更早的 117、D01）。本次我又抄了一遍（Data 层，十几分钟一次过）。
  建议落一条 `research/A04/probes/zero_solution.lean`（Data 层 + A02 层各一份），以后所有非空洞性探针直接 import。
* `regularizedNormDerivative` 现在**在合同层有消费者、在 `formalization/` 里仍零消费者**。
  它与 Z1 的两个导数半边（`regularized_sqrt_hasDerivWithinAt` / `regularized_sqrt_deriv`）合并为一条
  MAINT 观察项，等 C01/I01 的 `ζ` 步与 V3 的 `eq:criterion`/`higherOrderBound` 落地后一起裁决，
  现在不要删。
* V3 的内容 ATTEMPTS `:118-127` 已列清（`eq:criterion`、`higherOrderBound`（G3 `Gronwall.lean` 已在树里）、
  uniform restart），与 `REVIEW_G2B.md` §5.3 第 10 条一致，无冲突。
