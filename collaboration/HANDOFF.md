# HANDOFF.md — 可分发的并行工作包（快照：2026-09-15 12:55Z）

## 快照更新（2026-09-15 22:30Z，lead；表格于 2026-09-16 08:00Z 刷新：A01 局部理论装配完成，待合同措辞）

截至集成分支 `2c3df18`；最后合入的 lane PR 是 **#192**（lane 182）；**29 个合同**；owner 的 `main`（PR #161–#171）已并入集成分支（lane 184；同名模块改名为 `C01/EnstrophyIdentityRaw`、`A01/ConstructorDivergenceSlice`）。lead 现用 codex 工作流（`scripts/codex_lane.sh` / `codex_review.sh`）跑 lane 175–191，下面的 P 表状态以此为准：

| 包 | 状态（09-15 22:30Z） | 已落地 / 还缺 |
|---|---|---|
| P1 C01 能量/涡量 | **关闭**（owner V4 `C01.energy_absorption_v4` + 我们的 eq:RL2 V3） | 待一条 SIMP 去重 `Enstrophy`/`EnstrophyIdentityRaw` |
| P2 D01 齐次范数 | **关闭**（`D01.homogeneous_norm`，164） | — |
| P3 A05 临界嵌入 | **关闭**（165 + V2 合同 `A05.gradient_l6_v2`，181） | U4/U8（Λv 实现、∂_j v 半阶数据）lane 191 在做 |
| P5 R43 临界配对 | 175/182/191/214/216（#221）/219（#223）已合入：**eq:Rcritical1 对任意经典解无具名输入**（`rcritical1_of_classical'`）；221（力路径 G2/G3/G4 + a=0 bootstrap 探针）在做 | **可领：S4/S5 的 T_max 端点粘合（G5）** |——为经典解构造 `CriticalDatumPath`（`Section4/R43/CriticalPairing.lean:161`：整数阶数据 ⇒ 半阶齐次数据路径 `velocityHalf`/`velocityThreeHalf`/`laplacianHalf`/`advectionHalf`/`pressureHalf`/`forceHalf` 及其 `IsHomogeneousSliceDatum` 字段；入口 `D01/HalfOrder.lean`、`HomogeneousWitness.lean`、A05 U3 `homogeneousLeSobolev`）；闭合后 eq:Rcritical1 无条件 |
| P6 R44 | 166 拆分、218（#222，S1a J 权恒等式 + 力对偶）已合入；220（S1c 三线性）、222（S1b 能量恒等式）在做 | **可领**：S1d Young 吸收（等 S1a–c）、S2–S5 各行 |
| P7 A01 A3 | **闭合**：…202（#208）、203（#207）、204（#209）、205（#210）、206（#211）、207（#212）全部合入；`hb_of_base''` 无分析输入；`a01_constructor_unconditional` 探针在集成分支 | 剩合同注册（208/209/210，lead 在做）；**spec 问题**：`horizon_lower_bound` 的 H¹ 子句 vs 树支持的 H⁷（见 210 报告后 `NEXT_SESSION`） |
| P8 A01 B1 | **闭合**：161 R1、169 R2、178 R3、187 hfs（#193）、190 R4 联合光滑代表元（#194）全部合入 | — |
| P9 A01 B2/P4 | **闭合（条件于 hb）**：180（#190）构造器 + 189（#203）压力供给（194/195/197 三块 + Helmholtz 逆向）；探针 `a01_constructor_pipeline`：仅由 `hb` 得到 `ClassicalSolutionR` | — |
| P9b A04 延拓 | **闭合（固定力 + H⁷ 形状）**：213（#218）、215（#219）、217（#220）全部合入；延拓定理对 MemForceR 力无具名输入 | — （owner 的 `Restart` H¹/跨力措辞待 V2 决定） |
| P10/P11 R41D、SPEC | 174 已合入 | **可领**：R41D 拆分表 |

外部协作者请优先领 **P5 Parseval**、**P6**、**P10**（互不依赖、不碰 A01）；lane 号仍用 200–299。

## Integration update (2026-09-15)

This tree includes both dependency chains from PRs #161–#170. The package
assignments and counts below are an earlier snapshot. Before claiming work,
read `NEXT_SESSION.md`, the A01 implementation plan in
`research/A01/IMPLEMENTATION_PLAN_169.md`, and
`logs/MERGE_DEPENDENCIES_20260915.md`. C01 V4 and the conditional R43 maximal
endpoint estimate are present; merging does not close the remaining analytic
obligations or establish a successful cloud CI run.


> **本文件是一次性快照，不是活状态。** 截至：集成分支 `erenup/integration` 提交 `cefa150`；已合入集成分支的最后一条 lane PR 是 **#160**（lane 001–160 全部处理完）；`main` 含 #15（= 集成分支到 b7895f1）；owner 侧 **PR #161**（`codex/*` → `main`，覆盖 lane 158/160）尚未合入；本文件随 **PR #171** 进 `main`。26 条已注册合同、128 个 `Section4` 模块。之后的变化以 [`NEXT_SESSION.md`](../NEXT_SESSION.md) 和 `PLAN.md` §8 进度表为准；若某个包已被别人领走或做完，那里会写。

给愿意并行帮忙的人看的一页纸。总规划和状态看板在 [`PLAN.md`](../PLAN.md) §4–§5；规矩全文在 [`CLAUDE.md`](../CLAUDE.md)；活状态在 [`NEXT_SESSION.md`](../NEXT_SESSION.md)。本文件每个工作包都自成一体：目标、精确的 Lean 目标陈述、先读什么、树里已有什么、交付物、门禁、大小、依赖。

## 0. 五分钟须知

**环境**（自包含，不碰 `~/.elan`）：`bash scripts/lean-install.sh`（幂等）；之后每个 shell 先 `. scripts/lean-env.sh`；**`lake` 永远从 `verification/` 跑**，`LEAN_NUM_THREADS=6`。草稿 `research/<节点>/X.lean` 用 `cd verification && lake env lean ../research/<节点>/X.lean` 检查。

**一条 lane 的流程**：
1. 领一个 lane 号（外部协作者用 **200–299**，每人一段 20 个，见下表；填在你的 PR 里）。
2. `git worktree add .claude/worktrees/NNN-<节点>-<slug> -b erenup/NNN-<节点>-<slug> origin/erenup/integration`，在里面 `LEAN_SEED_DIR=<主仓路径> bash scripts/lean-install.sh`（从主仓复制编译产物，首次几分钟）。
3. 只加新文件：`formalization/NSFormalization/Section4/<节点>/<Module>.lean` + `research/<节点>/ATTEMPTS_<slug>.md`（正负例都记：证不出的路径、错误原文）+ `research/<节点>/axioms_<slug>.lean`（每个声明 `#print axioms`，必须恰好 `[propext, Classical.choice, Quot.sound]`；至少一个非空洞 `example`）。合同类包（V-注册）另加 `verification/Contracts/V<n>/…`、`Bindings/…`、`Tests/…`、`contracts.json` 一条（`ensure_ascii=False`）。
4. 门禁：`lake build NSFormalization.Section4.<节点>.<Module>`（静默）、`lake env lean` 该文件（0 输出）、axioms 文件、`make check`；碰 `verification/` 的包再跑 `scripts/gates.sh <模块>`（含 `make test`、`make test-mutations`）和 `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`。
5. PR 到 **`erenup/integration`**，标题 `[NNN-<节点>] 一句话`，正文四段：证了哪个定理（名字、精确陈述、常数）/ Lean 里现在有什么 / 缺口 / 跑了什么命令、什么结果。lead 派 opus reviewer 跑通、跑合并链门禁后合入，并记 `logs/AGENT_RUNS.csv` 与 `PLAN.md` 进度表。

**硬规矩**：不用 `sorry`/`admit`/`axiom`/`native_decide`；`set_option maxHeartbeats N in` 只能单声明、`N ≤ 400000` 并注释理由；不改 `paper/`；不改已冻结的 `Contracts/V1`、`Contracts/V2` 与既有 `Tests/*`（数学变了加新版本）；`Contracts/*` 只能 import `Mathlib`/`Contracts.*`（定义要逐字重写，绑定层用 `rfl` 桥；`ClassicalSolutionR` 结构体例外经 `Bindings.uniqueness_toA02`）；`Tests/` 是 `warningAsError`，不能 import HeliCorgi 的 `Formal.*`；不改既有模块（SIMP 包除外，且被消费的定理陈述逐字节不变）；宣称「树里没有」之前先 `grep -rn` 全部 `Section4/{D01,A03,A04,A01,C01}` 命名空间（`logs/LESSONS.md` 里踩过三次）；引用论文行号前 `sed -n` 核一遍。

**lane 号分配（外部）**

| 段 | 协作者 | 备注 |
|---|---|---|
| 200–219 | （待登记） | |
| 220–239 | （待登记） | |
| 240–259 | （待登记） | |
| 260–299 | 预留 | |

## 1. 工作包一览（串行 / 并行）

不同包之间**完全并行**；包内箭头是串行。

| 包 | 节点 | 一句话 | 大小 | 起步依赖 |
|---|---|---|---|---|
| P1 | A04 | `restartBeyond` → `lifespanInfiniteOfLocallyFinite` → A04 V3（R43/R44 消费）——**owner 团队已做（PR #161，以 `Restart`/`HigherOrderBound` 为具名假设），剩 V3 注册** | M+S+S → S | 等 #161 合入 |
| P2 | C01 | enstrophy 恒等式 E5→E6→E7 → `h2TimeIntegral` → C01 V4（R43/R44 消费） | M+M+S+M | 无 |
| P3 | A05 | `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}}` 的载体翻译 U1→…→U7 → A05 V2（R43/R44 消费） | M–L | 无 |
| P4 | D01 | G1 `dotHomogeneousENorm`（阻塞 R43/R44 陈述）；G3 半整数阶外力 datum 路径 | S；M–L | 无 |
| P5 | R43 | 自有 eq:Rcritical1（G7/S1）：配对恒等式、三线性估计、力项 | L | 陈述定稿等 P4 |
| P6 | R44 | 命题 4.4 拆分表 + S 行（照 159 的样子） | S+S | 无 |
| P7 | A01 | 构造子 B2 行：c6 散度 a.e. / 行 (v) `F ↔ f` 桥 / c9 压力 P3 | M / M–L / M | 无；三条互相并行 |
| P8 | A01 | 构造子 B1：`velocity_smooth` 的时间正则阶梯（最长杆） | L | 无 |
| P9 | A01 | (iv) 角不变性 `hinv`；`t = T` Grönwall 端点 | L / L | 无；两条互相并行 |
| P10 | MAINT | SIMP/tester：引用行号、去重、别名泛化、A01 新模块进合同闭包 | S–M | 无 |
| P11 | SPEC | R41D / R45 / R46 / R47 / G01 双盲陈述 | S–M 各 | 无 |

**协调说明（2026-09-15）**：owner 团队走 `codex/*` 分支直接 PR 到 `main`（PR #161 已覆盖 P1 与 158 的顶阶扩展）；外部协作者与我们走 `erenup/integration`。开新 lane 前先 `git fetch origin main` 看 owner 侧有没有同路径的 PR。

**串行骨干**：P8 → B2 装配（P7 汇合）→ `CarrierConstructorFull` → `HasAprioriBound` → `exists_local` → A02 `restart`（去掉 P1 的具名假设）→ R43/R44 装配（P1+P2+P3+P4+P5 汇合）→ R41。

## 2. 各包简报

### P1 · A04 寿命子句（`restartBeyond` + `lifespanInfiniteOfLocallyFinite` + A04 V3）

- **目标**：`research/A04/Spec.lean` 的两个字段，逐 token：
  - `restartBeyond : ∀ ν, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ, 0 < δ ∧ ∀ a f S u p, a ∈ initialClassR → MemForceR f → 0 < S → SolvesBelow ν a f S u p → (∀ t ∈ Ico 0 S, sobolevENorm 1 (u (t,·)) ≤ K) → BoundedIntoHOne (Icc 0 (S+1)) K f → forceSobolevENormL1 1 f ≤ K → ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f`
  - `lifespanInfiniteOfLocallyFinite`（`Spec.lean` 末尾，`∀ S, 0 < S → ofReal S ≤ T_max → squaredHTwoIntegral S u ≠ ⊤` ⟹ `T_max = ⊤`）。
- **关键**：`restartBeyond` 依赖 A02 的 `MaximalSolutionAPI.restart`（`research/A02/Spec.lean`），它依赖 A01 的局部存在性（树里未证）。先 grep 确认树里没有无条件 `restart`；然后把两个字段**以一条具名假设**（`restart` 字段原形）为前提证出 A04 自有部分：`t₀ ↑ S` 的极限、`δ` 与 `t₀`/`S` 无关、`maximalLifespanR` 的 sup 记账（`lifespan_ge_of_forall_shorter`，A02 转写）。模板：`formalization/FormalPatched/R3MildContinuation.lean:93,122`。
- **先读**：`research/A04/COMPARISON.md:131-152,185-191,216-217`；`research/A04/Spec.lean` 两字段 docstring；`Section4/A02/{Maximal,Patch,Order}.lean`；`Source/SmoothLifespan.lean:58,101,124`；`Section4/A04/HighContinuationIntegral.lean`（G2b，给 `[0,S)` 上一致 `H¹` 界的机器）。
- **交付**：`Section4/A04/RestartBeyond.lean`；然后 `Contracts/V3/EnergyHighPartial.lean`（extends V2 + 两字段）+ `Bindings/EnergyHighPartialV3.lean` + `Tests/EnergyHighPartialV3.lean` + `contracts.json` 第 27 条（具名假设在合同里必须以显式前提出现，不能是占位字段）。
- **大小**：M（R1）+ S（C1）+ S（注册）。串行 R1 → C1 → V3。

### P2 · C01 enstrophy 与 H² 时间积分（E5–E7 + C01 V4）

- **目标**：`research/C01/ENERGY_SPLIT.md` 行 E5/E6/E7 与 `enstrophyIdentity`（`Spec.lean:487`）、`enstrophyIntegralBound`（eq:RH1，`Spec.lean` H¹ 吸收）、`sobolevTwoFourier`、`h2TimeIntegral`（`Spec.lean:576,599`）。
- **树里已有**：全部前置机器——Ep/E3（`C01/MomentumCarrierB.lean`）、E4a 喷流路径（`JetPaths.lean`）、E4b（`PressureJetPath.lean`）、E4 装配（`EnergyDerivative.lean`）、能量恒等式与 eq:RL2（`EnergySpec.lean`、`EnergyBounds.lean`）；vendor `wordEnergy_hasDerivWithinAt` 在 `s = 1` 给 enstrophy 导数（`Euler/OrdinaryWordTime.lean:87`）；`field_directional_ibp`（分部积分）。
- **先读**：`ENERGY_SPLIT.md`（E5–E7 行的公式与引理指针）；`research/C01/REVIEW_E4.md`、`REVIEW_ENERGY_BOUNDS.md`；`Contracts/V3/EnergyAbsorptionPartial.lean`（V4 extends 它）。
- **交付**：`Section4/C01/Enstrophy.lean`（E5 `d/dt Σ‖∂ᵢu‖² = 2Σ⟪∂ᵢu, ∂ᵢ∂ₜu⟫ = −2⟪Δu, ∂ₜu⟫`，E6/E7 装配到 `enstrophyIdentity`），再 `H2Integral.lean`（`h2TimeIntegral`），再 V4 合同三件套 + registry。
- **大小**：M + M + S + M。串行。

### P3 · A05 临界嵌入的载体翻译（A05 V2）

- **目标**：`research/A05/Spec.lean:366` `velocityCriticalL3 : ‖u‖₃ ≤ C(1/2)·‖u‖_{Ḣ^{1/2}}`（datum 形齐次范数）。
- **树里已有**：Riesz 位势路线 `Paper1/SchwartzCriticalEmbedding.lean:57,171`（右端是齐次 datum）与全阶 `Source/FractionalRealization.lean:96,78`；`A05.gradient_l6`（`Contracts/V1/GradientL6.lean`）的 Bindings 写法可照抄。
- **先读**：`research/A05/COMPARISON.md:205-216`（U1–U7 单元表；只有 U9 完成）；`research/R43/REVIEW_SPLIT.md` §「A05」段。
- **交付**：`Section4/A05/CriticalL3.lean`（U1→U7）；`Contracts/V2/GradientL6.lean`（extends V1 + `velocityCriticalL3`）+ Bindings + Tests + registry。
- **大小**：M–L。串行 U1→U7→V2。**注意**：`Ḣ^{1/2}` 范数用 datum 形（见 P4 的 G1）；若 P4 未落地，先按 `research/R43/Spec.lean` 的本地 `def dotHomogeneousENorm` 写，V2 注册等 P4。

### P4 · D01 齐次范数定义 G1 与半整数阶外力路径 G3

- **G1（S，阻塞 R43/R44 的*陈述*）**：`research/R43/COMPARISON.md §4` 行 G1 给的精确形状 `def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ := ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSlice …}, …`（datum 形空间齐次范数）；先 grep `Section4/D01` 与 `B02/`（`homogeneous_partial` 已有齐次 datum 对象）看能否直接复用；落到 `Contracts/V1/Data.lean` 不能改（冻结），走 `Contracts/V2/Data.lean` 或新合同文件 + `rfl` 桥。定义类的东西不需要双盲，但要在 `research/D01/ATTEMPTS_G1.md` 记录与 `Data.dotHHalfENorm`（逐点 Fourier 积分，对非 L¹ 场退化为 0，**不能用**）的区别。
- **G3（M–L）**：`MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` 及齐次孪生（`MemForceR` 只给整数阶 datum 路径；需 `angularOrderLowering`/插值把 `m = 1` 路径降到 `1/2`）。先读 `research/R43/COMPARISON.md` G2/G3 行、`Section4/D01/ForceClass.lean`、`Section4/D01/HalfOrder.lean`、`LerayLowering.lean`。
- **交付**：`Section4/D01/HomogeneousNorm.lean`、`ForceHalfOrder.lean`；registry 视情况 D01 V4。

### P5 · R43 自有步骤：eq:Rcritical1（G7/S1）

- **目标**：`½(y²)' + (ν − C₀y)z² ≤ by`，`y = ‖u‖_{Ḣ^{1/2}}`、`z = ‖u‖_{Ḣ^{3/2}}`、`b = ‖f‖_{Ḣ^{1/2}}`（`04-whole-space.tex:97-99`），对 `ClassicalSolutionR` 于内点成立；外加临界路径的可导性（`HasSmoothCriticalPath`）。
- **拆法**（写进 `research/R43/R43_SPLIT.md` 的 S1 子行）：(a) 投影方程与 `Λu` 配对的恒等式（复用 C01 的配对/散度消去与 `EnergyDerivative.lean` 的导数装配模式，把 `wordEnergy` 换成齐次 `Λ` 权重）；(b) 三线性估计 `|⟨(u·∇)u, Λu⟩| ≤ C₀ y z²`（`04-whole-space.tex:98`；需 P3 的嵌入与 B02 的齐次工具）；(c) 力项 `|⟨f, Λu⟩| ≤ b y`。
- **先读**：`research/R43/R43_SPLIT.md`、`REVIEW_SPLIT.md`、`Section4/R43/Pieces.lean`（S2 bootstrap 已复用 `Paper1.critical_norm_bound`，`henergy` 假设就是这条不等式）。
- **大小**：L。可先做 (a)(c) 引理层；(b) 与最终陈述等 P3/P4。

### P6 · R44 命题 4.4 拆分

- 照 lane 159 的做法：`research/R44/Spec.lean`（`RCritical2API` 9 字段）+ `COMPARISON.md`（缺口 G1 J 权重恒等式、G2 eq:Rcritical2、G3 `H^{-1/2}` 力切片）→ 写 `research/R44/R44_SPLIT.md`（每行：Lean 形状、供给方、缺口、大小），并证 S 行（拼写钉、常数算术、bootstrap 复用）到 `Section4/R44/Pieces.lean`。先审计 `contracts.json`：哪些兄弟字段已注册。
- **大小**：S + S。

### P7 · A01 构造子 B2 行（三条并行）

目标结构：`CarrierConstructorFull`（`research/A01/REVIEW_CONSTRUCTOR_SPLIT.md` §3，以 `localTheory_on_prescribed_horizon` 的全部结论为假设）；拆分表 `research/A01/CONSTRUCTOR_SPLIT.md`（lane 158，合入后可见）。每条从柱面对 `(u, U)` + 候选 `velocity : SpaceTimeField` + `hslice : ∀ t, velocity (t,·) =ᵐ ⇑(U t)` 出发。
- **P7a c6 散度**（M）：`spatialDivergence velocity t x = 0`——先 a.e.：从 `value 1 (u t) ∈ divergenceFreeSpace 1 1 0` 经 `ordinaryLift` 下降（HeliCorgi 路线 `R3InversionConsistency.lean:139`）；逐点升级留给 c3。先读 `A01_SPLIT.md:107`、`C1B_SPLIT.md`、`Section4/A01/EulerPairing.lean`。
- **P7b 行 (v) 数据/外力桥**（M–L）：从 `a : SmoothL2Field Space`、`F : Icc 0 S → SmoothL2Field Space`（`hF` 喷流连续）造 `a' ∈ initialClassR`、`f' : SpaceTimeField` 满足 `MemForceR f'`、`MemL1Hm f'`，并把 `sobolevPath F hF` 与 `f'` 的 datum 路径对上。先读 `research/A01/REVIEW_APRIORI_ROWS.md` 行 (v)、`Section4/D01/ForceClass.lean:158`、`Section4/C01/JetPaths.lean`（`forcePath` 反向）。
- **P7c c9/c4 压力 P3**（M）：Helmholtz 分解 + 规范，`pressure_gradient : MemLp (∇p) 2` 与 `pressure_smooth`；先读 `A01_SPLIT.md` 单元 P3、`Section4/D01/Pressure*.lean`、`A04/PressureDrop.lean`。
- **交付**：各一个模块 `Section4/A01/Constructor{Div,Force,Pressure}.lean` + ATTEMPTS + axioms。

### P8 · A01 构造子 B1：`velocity_smooth`（最长杆）

- **目标**：`ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)`，`velocity` 为 `⇑(U t)` 的逐点代表元、联合时空光滑。
- **已知**：两个 vendor 代表元都不联合光滑（`CONSTRUCTOR_SPLIT.md` §2）；空间侧每个 `t` 的全阶 datum 已有（`ConstructorPieces.exists_isSobolevDatum_slice_of_cylinder`，158，`m ≤ q−2`；顶三阶由 `L2Descent.word_descent_ae_top` 补齐——158 审稿探针 `rev158_toporder.lean` ~45 行已证）；时间侧词路径连续的 S 阶梯已证（`rev158_wordpath.lean`）。
- **阶梯**（写进拆分表，逐级证）：(1) datum 路径 `t ↦ A_m(t)` 连续（选择连续 selection，`REVIEW_CONSTRUCTOR_SPLIT.md` §4）；(2) Duhamel 方程 ⇒ datum 路径在 `t` 上可导且导数为动量残差的 datum（复用 `A04/TimeDerivative.lean` 与 C01 的 `residualPath`）；(3) 归纳得 `C^k_t H^m_x` 全 `k, m`（`appendix-a-local-theory.tex:71-76`）；(4) Sobolev 嵌入 `H^m ↪ C^k_b` 给逐点联合 `C^∞`（`Paper3.angularBoundedRepresentative`、`Paper1/PeriodicH3RepresentativeBridge.lean`）。
- **大小**：L（多 lane，每级一条）。

### P9 · A01 供给侧 `hinv` 与 Grönwall 端点

- **P9a (iv) `hinv`**（L）：`HasAprioriBound`（`Section4/A01/Horizon.lean:106`）量化的 `u` 只受 Duhamel 方程约束；要证它自动角不变（唯一性 + 角平移不变性，或把 `HasAprioriBound` 的量化限制到不变子空间并证消费者仍闭合）。先读 `research/A01/REVIEW_APRIORI_ROWS.md`「Missing from the list」、`Section4/A01/ContinuationInvariant.lean`（`forced_ordinary_descent :147`）。
- **P9b `t = T` 端点**（L）：Grönwall 输出在闭端点（帽已有：`AprioriRows.kbnd_of_sup_bound_Icc_endpoint`；柱面端点免费：`rev149_cylinder_endpoint.lean`），即 eq:criterion 的硬端点——需要能量恒等式在 `T` 的极限。先读 `research/A01/REVIEW_APRIORI_ROWS.md` 行 (iii-b)。

### P10 · MAINT/SIMP 通道

- `research/C01/Spec.lean` 两处 `(:103)` → `(:104)`；`research/R43/COMPARISON.md`/`Spec.lean` 其余行号核对。
- `Section4/C01/EnergyBounds.lean` 的 `sqrt_energy_le_primitive'` 与 `Paper1/ScalarEnergy.lean` 约 45 行重复：把推广版上提到 Paper1 或让 Paper1 版成为其推论（消费者陈述不变）。
- `Section4/A01/SliceWiring.lean`：`velocitySliceSmoothL2` 别名与 `C01.velocityField_field` 重复；`sobolevENorm_slice_ne_top` 泛化到任意阶。
- A01 新模块（`OrderTwoCap`、`AprioriRows`、`CarrierWords`、`L2Descent`、`SliceWiring`、`ConstructorPieces`）不在任何合同闭包，`make test` 不编它们：打一个 A01 V2 合同包（把已无条件的先验行 `apriori_rows_of_hslice` 等以显式假设形式注册）。
- 规则：被消费的定理陈述逐字节不变；全部依赖模块重编；`scripts/gates.sh <触及模块>`。

### P11 · 未 spec 节点的双盲陈述

- R41D（定理 4.1 正方向，按外力子类参数化）、R45（推论 4.5）、R46（命题 4.6）、R47（定理 4.7）、G01（网格观测）。
- 规则 2：两个互不可见的 agent/人，只给论文第 4 节 + 附录 + `Contracts/V1/Data.lean` 的定义，各写一版 `research/<节点>/DraftA.lean` / `DraftB.lean`；第三人比对写 `COMPARISON.md`，定稿 `Spec.lean`；差异与上游缺口写成 G 表（照 `research/R43/COMPARISON.md §4`）。不写证明。

## 3. lead 收到 PR 后做什么

1. 派 opus reviewer（读 `.claude/skills/lane-review`）：陈述是否仍是论文那条、公理审计、非空洞、至少一个实质变异反例（不是删参数）。
2. 跑合并链：squash + rebase 到 `erenup/integration` → 合入 → 根目录全部 `Section4` 模块门禁 + `check_contracts --base-ref origin/main`。
3. 记 `logs/AGENT_RUNS.csv`、`PLAN.md` §8 进度表（UTC）、`NEXT_SESSION.md`；坑记 `logs/LESSONS.md`。
