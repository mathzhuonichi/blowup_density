# PLAN.md — 第 4 节 Lean 证明的总体计划

> **第 3 节（环面）的独立规划**：[`collaboration/SECTION3_PLAN.md`](collaboration/SECTION3_PLAN.md)（2026-09-16 快照：表示层决策、复用映射、T10–T24 DAG、并行/串行安排；先做完第 4 节再启动）。

## Integration snapshot (2026-09-15)

This tree consolidates PRs #162–#170 through their original dependency branches;
PR #161 delivers the combined result to `main`. It preserves the collaboration
layout from PR #171 and the A01 implementation plan from PR #170. The earlier
lane rows and contributor dashboards below are dated records: their pending-PR
labels and counts do not describe this integrated tree. There are 27 registered
contracts, including C01 V4. The R43 endpoint estimate retains its absorption
premise; A01 construction, A05, critical energy and unconditional continuation
remain open. See [the integration record](logs/MERGE_DEPENDENCIES_20260915.md).

The earlier erenup lane 158 implementation is superseded by the owner changes
in PR #161. Its independent review artifacts remain potential follow-up work.
The historical Claude execution settings are retained in
`logs/PLAN_HISTORY_20260913.md`; the Codex proof lanes recorded their own author
and compiler assignments in their validation reports.


更新 2026-09-15。状态看 [`NEXT_SESSION.md`](NEXT_SESSION.md)，规矩看 [`CLAUDE.md`](CLAUDE.md)，可分发的工作包看 [`collaboration/HANDOFF.md`](collaboration/HANDOFF.md)。
本文件：§1–§3 计划（只在计划变更时改）；§4 节点状态看板（每个里程碑后改）；§5 并行工作包（分发用摘要）；§6 并发与预算；§7 记录与恢复；§8 进度表（每次合入追加一行，带 UTC）；§9 发现与 DAG 修正记录（只追加）。2026-09-13 的旧 §4/§5 原文在 `logs/PLAN_HISTORY_20260913.md`。

## 当前 A01 方案（2026-09-15，lane 169）

详细执行依据：[H¹ 实施方案](research/A01/IMPLEMENTATION_PLAN_169.md)；独立 [Astra xhigh 审核原文](research/A01/REVIEW_H1_REFACTOR_169.md)。四个工作包为 H1-local、Persistence、Smooth carrier、Assembly；时间 bootstrap 和普通压力桥仍是实际分析义务。

- **立即下一项**：保留 lane 168 的 source/trace，完成实际正则化源对齐、有限 word 差值的 uniform Cauchy 和连续高阶极限，保留同一 T、原 a/f 与真实方程。
- **并行长期输入**：独立证明 H¹ 局部预算与 H¹→可用高阶范围的持久性桥。固定 q（如 q=6）的时间上升阶是中间成果，不能替代 H¹ 数据球统一时间。
- **最终依赖**：H¹ budget → 同预算连续全阶塔 → 真实 mild 的全阶时间动力学（含 t=0）→ 联合光滑与径向压力 → 同一 horizon 上完整 API。单独 mild 时间不能完成 `horizon_lower_bound`。
- 保留 `Horizon` 给定 S 的辅助用途和已证模块，复用现有 tower。A04 优先评估 m=3→H¹ 的真实最大族消费者；m≥3 前件与全阶合同保持。当前 `MemForceR` 已给全时 L¹/L²，无需为尾部预算新增 cutoff。
- 这次只修订方案；A01、A02 restart、A04 无条件延拓仍未完成。R43 G5 的条件性端点结果见平行 PR #168，其吸收前件和 A05/G7 仍开。

## 1. 总体：一棵树，两条脊柱，一个根

根 = 定理 4.1（两个阈值）。它由两条独立的脊柱汇合：

- **插入脊柱（I 链）**：U01 OpenAI packet → I01 packet 能量 → I02 向量势与光滑修正 → I03 同族缩放与负阶范数 → R42 定理 4.2 精确插入 → R41D 定理 4.1 正方向。
  这是最长路径（6 条边），但每步都有本地已有 Lean 部件可复用。
- **分析脊柱（A 链）**：U05 工具链 → A01 带外力 R³ 局部理论 → A02 唯一性与最大寿命 → A04 平方 H² continuation → C01 能量吸收 → R43/R44 命题 4.3/4.4 → R41 定理 4.1 反方向。
  这条更短（5 条边）但 **A01 是全项目最大缺口**：任何公开 Lean 库都没有带外力的 R³ 经典局部理论。

两条脊柱在 R42 处第一次相交（R42 需要 A02 的最大寿命），在 R41 处汇合。
D01（数据、外力、范数、压力的精确定义）是两条脊柱共同的地基，**所有陈述都用它的对象来写**。
其余节点（A05 临界嵌入、A03 tame 积、B01/B02 Bochner 逼近、G01 网格观测）是挂在脊柱上的叶子，
分别服务于 R43/R44、R46（命题 4.6）、R47（定理 4.7）。

DAG 的机器可读版在 `formalization/blueprint/tasks.json`；按最长路径分层得到的波次：

| 波次 | 节点 | 说明 |
|---|---|---|
| 0 | U01 U02 U03 U04 | 只是源码和文献，无工作 |
| 1 | **D01** U05 I01 | 可立刻开 |
| 2 | **A01** A05 I02 B01 B02 | A01 等 U05+D01 |
| 3 | A02 A03 I03 G01 | |
| 4 | A04 C01 **R42** | R42 = 定理 4.2 |
| 5 | R41D R43 R44 | 定理 4.1 的三块 |
| 6 | **R41** R46 | 定理 4.1、命题 4.6 |
| 7 | R45 R47 | 推论 4.5、定理 4.7 |

## 2. 顺序：陈述自顶向下 BFS，证明自底向上 DFS，合同处归并

三种遍历各管一件事，不要混：

1. **陈述用 BFS，自顶向下**。先把 D01 的定义定下来，然后从 R41 开始一层层往下写每个节点的 Lean 陈述
   （`Contracts/V1/*.lean` 草案），直到叶子。理由：接口不匹配是最贵的错误，
   父节点需要什么样的子结论，只有先写父节点才知道。这一步不写证明。
2. **证明用 DFS，自底向上，按 ready 前沿调度**。一个 lane 拿到一个节点后，把它拆成 ≤150 行的引理链，
   一条链推到 green 再开下一条（DFS），不要同时开一堆半成品。跨 lane 用 Kahn 前沿：谁的依赖全绿谁进队，
   并发上限 5。
3. **归并只在合同处发生**。父节点的证明只 import 子节点已注册的 `Bindings`，不复制子 lane 的证明文件。
   每个 lane 的 PR 只碰自己的 `Contracts/V1/<X>.lean`、`Bindings/<X>.lean`、`Tests/<X>.lean`、
   `formalization/NSFormalization/Section4/<X>/*.lean`，外加 `contracts.json` / `work_items.json` 各一行。
   这样 5 个 PR 之间几乎不冲突。

## 3. 局部：一条 lane 的标准流程

```
claim PR ──► spec ──► split ──► prove ──► bind+test ──► review ──► merge ──► 记账
```

- **claim**：`tasks.py claim <ID> erenup` + `render`，小 PR，防止两人重复。
- **spec（陈述保真）**：2 个互相看不到的 opus agent，只给论文第 4 节 + 附录 + D01 定义，各写一版 Lean 陈述。
  lead 比对；每处差异写进 `collaboration/tasks/<ID>.md`，定稿后再让第 3 个 agent 对照论文原文审一遍。
  产物：`Contracts/V1/<X>.lean`（只有 structure/字段，无证明）+ 任务卡里的"论文 ↔ Lean 对照表"。
- **split**：lead 把合同拆成引理清单，每条注明"复用哪个已有声明"（先查 `EXTERNAL_REUSE.md`，再派 subagent 搜源码）。
- **prove**：每条引理一个 prover agent，DFS。失败最多换思路重试 2 次，仍失败交回 lead 重拆。
  每次运行在 `logs/AGENT_RUNS.csv` 记一行（成功和失败都记），失败原因追加到任务卡 `## Attempts`。
- **bind+test**：写 `Bindings/<X>.lean`、`Tests/<X>.lean`，注册进 `contracts.json`，跑 `make check`、`make test`、`make test-mutations`。
- **review**：一个独立 reviewer agent 只做两件事：陈述是否仍与论文一致；公理审计输出是否只有标准 3 条。
  然后 PR 等 owner review（分支保护）。
- **记账**：`work_items.json` 状态、`PLAN.md` 进度表、`NEXT_SESSION.md`。

## 4. 节点状态看板（2026-09-15，集成分支 `erenup/integration`）

26 条已注册合同、128 个 `Section4` 模块、160 条 lane。合同全名前缀 `<节点>.`；拆分表在 `research/<节点>/`。「剩余」按论文证明还欠什么写，不按行政状态写。

| 节点 | 已完成（合同 / 关键模块） | 进行中 | 剩余（欠论文的什么） | 拆分表 |
|---|---|---|---|---|
| **D01** 数据、外力、范数、压力 | `datum_lemmas` v1/v2/v3（含 P2 压力喷流）；有限阶构造子定性（132）+ 定量 `‖A‖² ≤ 16^m·M`（145，锐 `4^m` 155）；Leray 投影、零解、25 个模块 | — | **G1** 齐次 `Ḣ^s` 范数的 datum 形定义 `dotHomogeneousENorm`（R43/R44 陈述依赖，S）；**G3** 半整数阶外力 datum 路径与非空洞（M–L）；D2 低阶下推（`A03.lowerDatum` CLM，M） | `FINITE_ORDER_SPLIT`、`P2_SPLIT`、`SL8_SPLIT` |
| **A01** 带外力 R³ 局部理论（关键链最大缺口） | `regularity_partial` v1；载体桥 C1a/C1b 全阶（140/151/153）；A2b 无条件续接（134）、力积分帽（137）、`horizon := S`（139）、Grönwall 实例（142）；A3-L1·k 算术 `Kbnd := 256R²T₀`（147）；`Icc` 加宽 + 反向范数比较（149）；切片接线、两条先验行打包（157）；18 个模块 | 158 构造子拆分（审稿 ACCEPT-WITH-NOTES，待并入探针证明后合入） | **B1** `velocity_smooth`（联合时空 `C^∞`，时间正则只能来自 Duhamel bootstrap T1/A2/A2b/A3，L）；**B2** 装配：c6 散度 a.e.（M）、c9/压力 P3（M）、行 (v) `F ↔ f` 数据/外力桥（M–L）；(iv) 角不变性 `hinv`（A2b，L）；`t = T` Grönwall 端点（L）；A3-Tm、H1、`Kbnd = Kbnd(R)` 的环 → 最终 `HasAprioriBound` 与 `LocalTheoryAPI.solution` | `A01_SPLIT`、`A3_SPLIT`、`C1B_SPLIT`、`CONSTRUCTOR_SPLIT`（158） |
| **A02** 唯一性与最大寿命 | `uniqueness`、`maximal_partial` v1/v2（`exists_maximal` 以 A01 存在性为显式假设）；8 个模块 | — | `restart` / `restart_datum` / `restart_force`（依赖 A01 存在性）→ A02 V3 | `research/R42/MAXIMAL_SPLIT` |
| **A03** tame 积与有界代表元 | `bounded_representative`、`tame_products` | — | `lowerDatum` CLM（服务 D2/C01 低阶） | — |
| **A04** 平方 H² continuation | `energy_high_partial` v1/v2（eq:Rhigh、G2/G2b `eq:highcontinuation`）；零解见证；21 个模块 | 160 `restartBeyond` + `lifespanInfiniteOfLocallyFinite`（被限流中断，工作树干净，待重启） | **R1** `restartBeyond`（以 A02 `restart` 为具名假设，M）；**C1** `lifespanInfiniteOfLocallyFinite`（S）→ **A04 V3**（R43 消费）；G1-SL1 `∂ₜu` 的 datum（需 A01 `C^∞`） | `G1_SPLIT`、`SL5_SPLIT`、`COMPARISON.md:216-217` |
| **A05** 临界嵌入 | `gradient_l6` v1（`‖∇u‖₆`） | — | `velocityCriticalL3`（`‖u‖₃ ≤ C·‖u‖_{Ḣ^{1/2}}`；Riesz 路线在 `Paper1/SchwartzCriticalEmbedding.lean`，载体翻译 U1–U7，M–L）→ **A05 V2**（R43/R44 消费） | `research/A05/COMPARISON.md:205-216` |
| **C01** 能量吸收 | v1（H¹ 吸收五字段）、**v2 能量恒等式无条件**（150/152）、**v3 eq:RL2**（154/156）；12 个模块 | — | **E5–E7** enstrophy 恒等式 → `enstrophyIntegralBound`（eq:RH1）、`sobolevTwoFourier`、`h2TimeIntegral` → **C01 V4**（R43/R44 消费）；G4 齐次切片可积、G5 `S = T_max` 端点 | `ENERGY_SPLIT` |
| **B01/B02** Bochner 逼近、齐次 | `bochner_partial`；`homogeneous_partial` v1/v2 | — | 各自 `REMAINING_SPLIT`/`U2_SPLIT`/`U7_SPLIT` 的剩余行 | `research/B01/U7_SPLIT`、`research/B02/REMAINING_SPLIT` |
| **I01/I02/I03** 插入脊柱 | `packet`、`correction` v1/v2、`scaling` | — | 各拆分表剩余行 | `research/I02/`、`research/I03/` |
| **R42** 定理 4.2 | `insertion_family`、`insertion_lifespan` v1/v2 | — | `LIFESPAN_SPLIT`/`MAXIMAL_SPLIT` 剩余（含 `sobolev` 字段非紧支路径） | `research/R42/` |
| **R43** 命题 4.3 | spec（037/038 盲比对）；拆分 S1–S6 + `Pieces.lean`（G6 幂拼写、G8 半径/吸收门、S2 复用 `Paper1.critical_norm_bound`）（159） | — | **上游三条未证子句**：A04 V3、C01 V4、A05 V2；**G1**（阻塞陈述）；自有 **G7/S1** eq:Rcritical1（三线性估计 + 配对恒等式，L）；G2/G3/G4/G5 | `R43_SPLIT`、`COMPARISON.md §4` |
| **R44** 命题 4.4 | spec（046/047 盲比对） | — | 与 R43 同型拆分（`RCritical2API` 9 字段；G1 J 权重恒等式、eq:Rcritical2、`H^{-1/2}` 力切片）；同一批上游 | `research/R44/COMPARISON.md` |
| **R41** 定理 4.1 | `threshold_arithmetic` v1 | — | 装配：等 R42、R43、R44、R41D | — |
| **R41D / R45 / R46 / R47 / G01** | — | — | 尚未 spec（needs-specification；按规则 2 双盲陈述） | — |

**关键链现状**：D01 ✅ → A01（B1 是全项目最大阻塞，其余先验行已闭合到「一条具名构造子」）→ A02（`restart` 等 A01）→ A04（R1/C1 可先以假设形式做）→ C01（E5–E7）→ R43/R44（三条上游 + G1 + 自有 G7）→ R41。

## 5. 并行工作包（可分发；详细简报见 `collaboration/HANDOFF.md`）

规则：每个工作包一条 lane、一个 worktree、一个 PR 到 `erenup/integration`，reviewer 跑通后合入；**外部协作者用 lane 号 200–299**（每人一段 20 个，在 `HANDOFF.md` 登记），避免与 lead 的 1xx 撞号。串行链内部按箭头顺序做，不同链之间完全并行。

| 包 | 节点 | 内容 | 大小 | 依赖 | 并行性 |
|---|---|---|---|---|---|
| **P1** | A04 | R1 `restartBeyond`（以 A02 `restart` 为具名假设）→ C1 `lifespanInfiniteOfLocallyFinite` → A04 V3 合同 | M + S + S | 无（A02 `restart` 作显式假设） | 独立链 |
| **P2** | C01 | E5 enstrophy 导数 → E6 → E7 → `enstrophyIntegralBound`/`sobolevTwoFourier`/`h2TimeIntegral` → C01 V4 合同 | M + M + S + M | 无（E1–E4b 机器已在树里） | 独立链 |
| **P3** | A05 | `velocityCriticalL3` 的载体翻译 U1 → … → U7 → A05 V2 合同 | M–L | 无（Riesz 路线已在树里） | 独立链 |
| **P4** | D01 | G1 `dotHomogeneousENorm` 定义 + `Data` 侧注册；G3 半整数阶外力 datum 路径/非空洞 | S + M–L | 无 | 独立；**阻塞 R43/R44 陈述** |
| **P5** | R43 | 自有 G7/S1：eq:Rcritical1（配对恒等式、三线性估计 `|⟨(u·∇)u,Λu⟩| ≤ C₀ y z²`、力项） | L | 陈述定稿需 P4；装配需 P1/P2/P3 | 可先做引理层 |
| **P6** | R44 | 命题 4.4 拆分（同 159 的做法）+ S 行 | S + S | 无 | 独立 |
| **P7** | A01 | B2 行：c6 散度 a.e.（M）；行 (v) `F ↔ f` 桥（M–L）；c9/P3 压力（M） | M / M–L / M | 无（各自独立） | 三条互相并行 |
| **P8** | A01 | B1 时间正则阶梯：词路径连续 S 阶梯已有（158 审稿探针）→ Duhamel 方程给 datum 路径的时间连续/可导 → 联合 `C^∞` | L | 无起步依赖 | 独立；最长杆 |
| **P9** | A01 | (iv) `hinv`（A2b：`HasAprioriBound` 量化的 `u` 的角不变性）；`t = T` Grönwall 端点 | L / L | 无 | 两条互相并行 |
| **P10** | MAINT | SIMP/tester 通道：`Spec.lean` 引用行号、`sqrt_energy_le_primitive'` 与 Paper1 去重、`SliceWiring` 别名泛化；把 A01 新模块打进一个合同闭包（A01 V2 bundle） | S–M | 无 | 独立 |
| **P11** | SPEC | R41D / R45 / R46 / R47 / G01 的双盲陈述（规则 2） | S–M 各 | 无 | 独立 |

**串行骨干**（不能并行的部分）：P8 → B2 装配（P7 各行汇合）→ `CarrierConstructorFull` → `HasAprioriBound` → `exists_local` → A02 `restart`（去掉 P1 的假设）→ R43/R44 装配（P1+P2+P3+P4+P5 汇合）→ R41。

## 6. 并发与预算（2026-09-14 起）

- lead：本会话（Fable 5.1）。只做拆任务、比对、归并、记账、跑门禁；不亲自写长证明（docstring/记录级修正可以）。
- worker：`prover` agent（Opus 4.8）；reviewer：`general-purpose` + `model: opus`（Opus 5）。每个 subagent 任务限定在一个引理或一个陈述。
- **并发上限 2–3 个 subagent（含 reviewer）**（API 限额，2026-09-14 用户指示），关键链优先；router 429 窗口时退避 10 → 30 → 60 分钟，重启前先用 1 秒探针试上游，被 kill 的 agent 用 SendMessage resume（工作树改动都在）。
- **CI 无额度 → 本地替代**：每条合并链跑 `scripts/gates.sh` + 全部 `Section4` 模块编译 + `check_contracts --base-ref origin/main`；并定期整跑 CI 三步对 `main`（`check_contracts` / `build_changed_lean` / `test_contract_mutations --skip-build`，日志 `tmp/ci_equiv_main.log`）。
- 外部协作者：lane 号 200–299，流程与门禁同 `collaboration/HANDOFF.md`；他们的 PR 由 lead 跑 reviewer + 门禁后合入。

## 7. 记录与恢复（防 context 压缩）

- `PLAN.md`：全貌 + 进度表（每次合入更新）。
- `NEXT_SESSION.md`：每次收工必更新，新 session 第一件事读它。
- `collaboration/tasks/<ID>.md`：每个任务的对照表和 `## Attempts`（正负例）。
- `logs/AGENT_RUNS.csv`：每次 subagent 运行一行。
- 本地会话原始记录在 `~/.claude/projects/-data-8T-ping-blowup-density/*.jsonl`。
  细节丢失时派一个 subagent 用 grep 在里面找（关键词：任务 ID、引理名、文件名），不要整文件读进主上下文。

## 8. 进度表

| 节点 | 状态 | UTC | 合同 | PR | 备注 |
|---|---|---|---|---|---|
| R41 算术部件 | 绿 | — | `R41.threshold_arithmetic` V1 | #1 | owner 提交，只含算术 |
| 001-MAINT-setup | 已合入 integration | 09-13 0417Z | — | #4 | CLAUDE.md / PLAN / scripts / .gitignore |
| 002-D01a-definitions | 已合入（REJECT 留档） | 09-13 0448Z | — | #7 | 草案 A 漏了 F_R 的 C^∞ 条件 → 定理 4.1(ii) 变假；归并 lane 修 |
| 003-D01b-definitions | 已合入（ACCEPT-WITH-NOTES） | 09-13 0459Z | — | #9 | 草案 B 带 C^∞；major：CompletedDense 量词过宽；归并基底 |
| 004-U05-toolchain-probe | 已合入（ACCEPT-WITH-NOTES） | 09-13 0451Z | — | #8 | 88 模块闭包 84 过、1 错（NNReal.mk）、3 阻塞；reviewer 实测 srcDir+roots 方案可行 |
| 005-I01-packet-energy | 已合入（ACCEPT-WITH-NOTES） | 09-13 0448Z | — | #5 | 27 字段 PacketAPI；11 条是 OpenAI 直接投影 |
| 006-SPEC-section4-statements | 已合入（ACCEPT-WITH-NOTES） | 09-13 0448Z | — | #6 | 1175 行台账；DAG 修正建议见下 |
| 007-I01-contract | 已合入（ACCEPT-WITH-NOTES，已修） | 09-13 0534Z | **`I01.packet` V1 已注册** | #12 | 第一条 PDE 合同；27 义务全证；20 个内联定义 + 19 个 rfl 桥；标准 3 公理 |
| 008-I02-correction-spec | 已合入（ACCEPT-WITH-NOTES） | 09-13 0525Z | — | #10 | 76 字段 CorrectionAPI；3.4/3.5 的 R³ 内容本地已基本证完，缺 4 小项 |
| 011-I02-contract | 已合入 | 09-13 0819Z | **`I02.correction` V1 已注册（rebase 后门禁全绿）** | #19 | 73 义务全证；范数已搬到 Data.lean 的 ℝ≥0∞ 规范范数；多一条论文自带的假设 π 光滑；参考解开板光滑桥因单切片消失 |
| 016-A02-spec | 已合入 | 09-13 0820Z | — | #22 | ACCEPT-WITH-NOTES 已修（压力基点归一化字段；U1 拆成 M+L）；本地 `classical_uniqueness_on_Icc` 同载体；加边 A03 → A02 |
| 017-A03-spec | 已合入 | 09-13 0820Z | — | #20 | ACCEPT-WITH-NOTES 已修；标量理论本地已完整，缺实向量/张量层与实性稳定性；U2 依赖 D01 L2（风险） |
| 018-B01-spec | 已合入 | 09-13 0820Z | — | #21 | ACCEPT-WITH-NOTES 已修；主字段已由本地源码覆盖（所有 s、q<∞）；缺口只剩时间 C^∞ 搬运；无 L 单元 |
| 012-SPEC-ledger-fixes | 已合入 | 09-13 0545Z | — | #13 | 台账 v2：12 处修正 + DAG 提案 + CHANGELOG |
| 010-U05-port | 已合入（ACCEPT-WITH-NOTES） | 09-13 0529Z | — | #11 | 88 模块全部编过；补丁只在 4 个副本、1 处 have；vendor 零改动；make snapshot 待 owner 重拍 |
| 009-D01-reconcile | 已合入（ACCEPT-WITH-NOTES，已修） | 09-13 0604Z | **`Contracts/V1/Data.lean`**（定义合同，不注册） | #14 | 63 个定义；**合同 import 精确白名单 6 本地 + 1 上游模块，待 owner 批准** |
| 013-A01-spec | 已合入 | 09-13 0658Z | — | #17 | ACCEPT-WITH-NOTES 已修；路线：OpenAI/本地 forced Duhamel 主干 + HeliCorgi 压力；缺的关键单元是阶数 m 的 continuation + 跨阶一致（A2b）；15 单元 3S/7M/5L |
| 014-A05-spec | 已合入 | 09-13 0658Z | — | #16 | ACCEPT-WITH-NOTES 已修（端点 3/2）；L⁶ 界几乎现成；L^{p_a} 骨架需搬约定（(2π)^{-a}）；Λ 做关系 |
| 015-I03-spec | 已合入 | 09-13 0820Z | — | #18 | ACCEPT-WITH-NOTES 已修（scalingStatement 补 7 条前提可满足；Prop 3.3 转运 3 字段）；U7c 是 R46 阻塞点 |
| 019-A05-l6-contract | 已合入 | 09-13 0942Z | **`A05.gradient_l6` V1 已注册** | #23 | 论文原形；Hessian–Laplacian 等式；无 Fourier；R43/R44 消费它还需 datum ⇒ jets + 时间切片提取（下一条 D01 lane） |
| 020-D01-hm-datum | 已合入 | 09-13 0942Z | — | #24 | **已证** jets ⇒ datum，任意实数阶、无紧支撑；29 定理标准公理；ACCEPT-WITH-NOTES 已修；余：datum ⇒ jets、双边范数、时间路径 |
| 021-I03-contract | 已合入 | 09-13 0944Z | **`I03.scaling` V1 已注册** | #26 | 31 字段全证（等式处证等式；力收敛 q=1,2）；HomogeneousScalingAPI 未注册；定理 4.2 不依赖齐次界，R46 只卡 U7c |
| 022-B02-spec | 已合入 | 09-13 0943Z | — | #27 | 20 字段；范围 −3/2 < s ≤ 0；常数经 reviewer 独立推导一致；齐次实现半边为空（单元 6 = U7c，XL，建一次共用） |
| 023-A03-l2linf-contract | 已合入 | 09-13 0943Z | **`A03.bounded_representative` V1 已注册** | #25 | H² jet 形式，逐点 + ess-sup；复用 OpenAI `smooth_pointwise_le_H2`；datum 形式待 D01 反向 |
| 024-D01-homogeneous-witness | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1150Z | — | #28 | **已证**：Schwartz/C_c^∞ 场在所有 s > −3/2 有齐次数据 + 范数恒等式；任意实数阶唯一性（L7）；差分；路径提升缺强可测；56 声明标准公理；发现 B02 `homogeneousDatumSub` 原样为假 |
| 025-D01-datum-to-jets | ACCEPT，已合入 | 09-13 1151Z | — | #29 | **已证**：`MemHInfty ↔ SmoothSquareIntegrableJets`、定量 jet 界（一个 (2π)^m）、含 t=0 的切片提取、`MemHInfty` 导数封闭；两条 jet 合同已从 `ClassicalSolutionR` 端到端应用成功；L2 全部关闭 |
| 026-A03-tame-contract | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1149Z | **`A03.tame_products` V1 已注册** | #31 | datum 层：eq:Rproduct(1)、eq:algebra、eq:tame（H² 低阶因子）、差分、对流；新证实子空间在完备乘法下稳定；3 字段待 datum⇒jets（025）后补；8 处 maxHeartbeats 待 reviewer 评估 |
| 027-R42-assembly-contract | ACCEPT 已修，已合入 | 09-13 1150Z | **`R42.insertion_family` V1 已注册（第 7 条）** | #30 | 定理 4.2 除寿命同定外全部子句；K→K_* 在 R42 侧以缩小 ε₀ 解决；**缺口：无合同提供 g_ε ∈ F_R（时间正则性）**，连寿命 ≥ T 都无法陈述 → 028 |
| 028-D01-forceclass-closure | ACCEPT，已合入 | 09-13 1151Z | — | #32 | **已证**：F_c ⊆ F_R（datum 路径时间 C^∞）、F_R/F_c 加法封闭、g+H_ε+F_ε ∈ F_R（R42 可直接消费）；23 定理标准公理；余：u_ε 的 `ClassicalSolutionR.sobolev`（非紧支） |
| 029-I02-v2-thetaradius | ACCEPT，已合入 | 09-13 1150Z | **`I02.correction_v2` 已注册** | #33 | `extends` V1 + 1 字段 `K ⊆ plateau`；兼容绑定 V1-of-V2；`force_carrier_subset_ball` 直接证出 021/027 说"无法履行"的前提；政策脚本零改动 |
| 030-A04-spec | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1244Z | — | #35 | 平方 H² continuation 适配器（∫‖u‖²_{H²} < ∞ ⇒ 高阶界 + 越过 S 的一致重启；R43/R44 的关键路径） |
| 031-C01-spec | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1245Z | — | #36 | 常规能量与 H¹ 吸收（eq:RL2、eq:RH1；R43/R44 用） |
| 032-A02-restrict-order | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1244Z | — | #34 | A02 单元 U4+U6：`restrict`/congruence/`pressure_normalization` 与六个序论字段（无分析） |
| 033-A02-energy-u1a | ACCEPT-WITH-NOTES，已合入（去重 → 040） | 09-13 1245Z | — | #38 | A02 单元 U1a：`ClassicalSolutionR` ⇒ `UniformFiniteEnergy (Icc 0 T')` |
| 034-D01-lemma-contract | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1244Z | **`D01.datum_lemmas` V1（第 10 条）** | #37 | 把 020/024/025/028 的 D01 引理收成合同 `D01.datum_lemmas`（jets⇔datum、齐次见证、F_R 闭包、切片提取），进 `make test` 闭包 |
| 035-B01-units-1-3 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1444Z | — | #39 | B01 单元 1–3（R46 实际消费的三条：Schwartz/紧支稠密 + 完备化代表元），`Section4/B01/` |
| 036-B02-units-3-4 | ACCEPT-WITH-NOTES，已合入 | 09-13 1445Z | — | #42 | B02 单元 3+4（低频权重可积性/积分值；角 Fourier 上确界界），`Section4/B02/` |
| 037-R43-spec-A | 盲稿 A+B 比对调和完成，已合入 | 09-13 1315Z | — | #40 | `RCritical1API` 4 字段（B 形状）；上游缺口 G1–G7 见 `research/R43/COMPARISON.md` §4 |
| 038-R43-spec-B | 已合入（经 037） | 09-13 1315Z | — | #40 | 命题 4.3 spec 盲稿 B（与 037 互不可见） |
| 039-A04-units-f1-n1 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1444Z | — | #41 | A04 单元 F1（`MemForceR` ⇒ L¹_tH^m / 有界 H¹ 力）+ N1（被积函数连续性），`Section4/A04/` |
| 040-SIMP-A02-dedupe | ACCEPT-WITH-NOTES，已合入 | 09-13 1444Z | — | #43 | A02 四模块的 simplifier + tester：Restrict §0 → import SolutionClass；Energy §1–2 → D01 DatumToJets；conformance/negative 检查 |
| 041-A04-unit-g3 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1453Z | — | #45 | A04 单元 G3：连续变系数 Grönwall（纯 ODE 引理，Mathlib 缺），`Section4/A04/Gronwall.lean` |
| 042-D01-halforder-force-norms | ACCEPT-WITH-NOTES，已合入 | 09-13 1445Z | — | #44 | D01 G3+G2：`MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤`（及齐次孪生）、路径级 Ḣ^{1/2} ≤ H^{1/2}；`Section4/D01/HalfOrder.lean` |
| 043-A04-unit-z1 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1453Z | — | #46 | A04 单元 Z1：带线性项的 ζ-正则化开方微分不等式（推广 `Paper1.sqrt_energy_le_primitive`），`Section4/A04/Regularized.lean` |
| 044-C01-unit-u6 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1453Z | — | #47 | C01 单元 U6（无 U1 依赖）：L³ 插值 + `laplacianSqENorm` 桥，`Section4/C01/` |
| 045-C01-unit-u2 | ACCEPT-WITH-NOTES，已合入 | 09-13 1453Z | — | #48 | C01 单元 U2：`MemForceR f ⇒ MemLp (slice f t) 2` + `t ↦ ‖f(t)‖₂` 连续（`forceTimeRegularity`），`Section4/C01/ForceSlices.lean` |
| 046-R44-spec-A | 盲稿 A+B 比对调和完成，已合入 | 09-13 1453Z | — | #49 | `RCritical2API` 9 字段；缺口 G1（J 权重恒等式）、G2（eq:Rcritical2）、G3（H^{-1/2} 力切片）、G5（幂拼写）见 `research/R44/COMPARISON.md` §4 |
| 047-R44-spec-B | 已并入 046 | — | — | — | 命题 4.4 spec 盲稿 B（与 046 互不可见，同样输入） |
| 048-B01-units-6-8 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1507Z | — | #51 | B01 单元 6（`separatedAssembly`）+ 8（`spatialApprox`），`Section4/B01/Separated.lean` |
| 049-A02-unit-u1b | ACCEPT，已合入 | 09-13 1454Z | — | #50 | A02 单元 U1b：`ClassicalSolutionR` 在 `Icc 0 T'` 上的 `‖u‖` 与 `‖∇u‖` 一致上界（经 `D01.datum_lemmas` + `A03.bounded_representative`），`Section4/A02/Bounds.lean` |
| 050-C01-units-u1-u3 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1507Z | — | #52 | C01 单元 U1（`velocityJets`，经 `D01.datum_lemmas` 现为 S）+ U3（演化打包成 `SmoothL2Field` 路径），`Section4/C01/{VelocityJets,Evolution}.lean` |
| 051-B02-unit-1 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1521Z | — | #56 | B02 单元 1：环形截断 + 光滑化（`annularRestriction`、`annularSmoothing`），`Section4/B02/Annular.lean` |
| 052-A02-units-u2-u3 | ACCEPT，已合入 | 09-13 1507Z | — | #53 | A02 单元 U2（`velocity_unique` 经 `classical_uniqueness_on_Icc` + U1a + U1b）+ U3（`pressure_gauge`）；**叠在 049 分支上**，`Section4/A02/Uniqueness.lean` |
| 053-A04-unit-d1 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1510Z | — | #54 | A04 单元 D1：`HasSmoothSobolevPath` ⇒ 平方 datum 范数的导数 `2⟪G t, G' t⟫`，与 `sobolevNormAt = ‖G‖`；**叠在 039 分支上**，`Section4/A04/DerivNorm.lean` |
| 054-D01-datum-lemmas-v2 | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1515Z | **`D01.datum_lemmas_v2`（第 11 条）** | #55 | `D01.datum_lemmas` **V2**：`extends` V1 + 042 的 `forceSobolevENorm_ne_top` 字段；Bindings import `HalfOrder`（进合同闭包） |
| 055-D01-unit-l9c | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1544Z | — | #59 | D01 单元 L9(c)：eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` 与压力梯度的全阶 jet（C01 U4/U7 的根缺口），`Section4/D01/Pressure.lean` |
| 056-A04-g1-split | ACCEPT-WITH-NOTES ×2 已修，已合入（D2 已证） | 09-13 1615Z | — | #61 | A04 单元 G1（forced viscous eq:Rhigh 在 datum 载体上；= A01 A2）的 spec 级拆分：给定 D1/D2/动量/tame 积，列出子引理与精确陈述，证能证的 S 级子步 |
| 057-A02-uniqueness-contract | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1534Z | **`A02.uniqueness`（第 12 条）** | #57 | 注册 `A02.uniqueness`（`UniquenessAPI`：`velocity_unique` + `pressure_gauge`，绑定 052/049/033 的定理，`ClassicalSolutionR` 逐字段桥） |
| 058-A02-units-u5-u9 | ACCEPT，已合入 | 09-13 1535Z | — | #58 | A02 单元 U5（`patch`，取更长 horizon）+ U9（`lifespan_le_of_unbounded`，经 U1b 的 H² 上界机制），`Section4/A02/Patch.lean` |
| 059-B02-unit-7 | ACCEPT-WITH-NOTES，已合入（含角约定 Plancherel） | 09-13 1627Z | — | #62 | B02 单元 7：`lowHighSplit`（低/高频拆分，`k ∈ L¹ ∩ L²`，角坐标约定），`Section4/B02/LowHigh.lean` |
| 060-B02-unit-8 | ACCEPT-WITH-NOTES，已合入 | 09-13 1628Z | — | #63 | B02 单元 8：`cutoffLebesgue` + `spatialApproxHomogeneous`（对角逼近），`Section4/B02/Cutoff.lean` |
| 061-A02-maximal-partial-contract | ACCEPT，已合入 | 09-13 1605Z | **`A02.maximal_partial`（第 13 条）** | #60 | 注册 `A02.maximal_partial`：`MaximalSolutionAPI` 中已证的 10 个字段（六个序论 + `restrict` + `pressure_normalization` + `patch` + `lifespan_le_of_unbounded`），`horizon_le_lifespan` 带 ⟪A01:solution⟫ 显式假设 |
| 062-D01-p2-split | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1632Z | — | #64 | 义务 P2（Leray 补投影在实角约定全空间 H^m 上有界）的拆分 + S 级子步：盘点 HeliCorgi 港口的 `r3LerayComplementL2`/`R3LerayRealLinearBridge`，列出实线性/约定/分布↔经典/L²→H^m 四座桥的精确陈述 |
| 063-B01-unit-7-split | ACCEPT-WITH-NOTES，已合入（#67；lead 改坏 docstring，070 热修） | 09-13 1655Z | — | #67 | B01 单元 7（`temporalApprox` / `SeparatedTemporalDense`，L）的拆分 + S 级子步：`dense_span_separatedLp` 在 `H := RealVectorSobolev s` 的实例化、`Submodule.span` 展开、`Lp` 商到代表元 |
| 064-A02-unit-u7 | ACCEPT-WITH-NOTES，已合入 | 09-13 1647Z | — | #65 | A02 单元 U7：`exists_maximal` + `maximal_unique`（以 ⟪A01:solution⟫ 为显式假设；S ↑ T_max 的有向并 + U2/U3/U4 归一化的相干性），`Section4/A02/Maximal.lean` |
| 065-A04-sl2-momentum | ACCEPT-WITH-NOTES，已合入 | 09-13 1654Z | — | #66 | A04 子引理 SL2：动量方程的 datum 形式（用 D2 + 钉代表元技巧把 `∂ₜu = f − (u·∇)u + νΔu − ∇p` 提升到 `RealVectorSobolev m` 的 datum 等式），`Section4/A04/MomentumDatum.lean` |
| 066-A04-sl3-laplacian | 已合并 | 09-13 1749Z | #73 | #73 | A04 子引理 SL3：Laplace 配对恒等式 `⟪G, datum(Δu)⟫ ≤ −‖∇u‖²_{H^m}` 在 datum 载体上（datum 侧阶移 / `∂ⱼ` 的 datum = `iξⱼ`·datum，与 P2 共用），`Section4/A04/LaplacianDatum.lean` |
| 067-D01-p2-sl7a | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1705Z | — | #69 | P2 子引理 SL7a：零阶 Plancherel 种子 `MemLp z 2 ⟹ ∃ A, IsSobolevDatum 0 z A`（用 059 的 `angular_plancherel`；从 `pressure_gradient` 出发给 ∇p 一个零阶 datum），`Section4/D01/OrderZeroDatum.lean` |
| 068-B02-unit-6 | 已合并 | 09-13 1752Z | #74 | #74 | B02 单元 6：`lebesgueHomogeneousDatum`（k ∈ L¹∩L² 在 −3/2 < s ≤ 0 的齐次 datum 存在 + 范数子句）与 `homogeneousDatumSub`，用 059 的角 Plancherel，`Section4/B02/LebesgueDatum.lean` |
| 069-A02-maximal-partial-v2 | ACCEPT，已合入 | 09-13 1716Z | **`A02.maximal_partial_v2`（第 14 条）** | #70 | `A02.maximal_partial` **V2**：`extends` V1 + `maximal_unique`（无条件）+ `exists_maximal`（以 A01 存在性为显式假设），绑定 064 的 `Maximal.lean` |
| 070-MAINT-hotfix-temporal | 已合入 | 09-13 1702Z | — | #68 | 热修 063 的 docstring（lead 手改吞掉 `-/`）；全量门禁 58 模块绿 |
| 071-B01-partial-contract | ACCEPT-WITH-NOTES 已修，已合入 | 09-13 1727Z | **`B01.bochner_partial`（第 15 条）** | #71 | 注册 `B01.bochner_partial`：`BochnerApproxAPI` 中已证的字段（χ 五条 + 单元 1–3、6、7、8），排除单元 9 的两条保真字段与 `SeparatedCompactDense` 打包 |
| 072-R42-lifespan-split | 已合并 | 09-13 1745Z | #72 | #72 | R42 剩余的寿命同定子句拆分 + S 级子步：用已注册的 `A02.maximal_partial`（`lifespan_le_of_unbounded`、`lifespan_ge_of_forall_shorter`）把定理 4.2 的 `T_max(u_ε) = 1` 拆成「包的 L^∞ 爆破 ⇒ ≤ 1」与「每个 S<1 上有解 ⇒ ≥ 1」，列出缺的 `sobolev` 字段（非紧支 u_ε）与 `hg : MemForceR g` |
| 073-D01-p2-sl3-multiplier | 已合并 | 09-13 1822Z | #77 | #77 | P2 子引理 SL3：Leray 补投影的算子值 L² 乘子 CLM（HeliCorgi `R3LerayPointwiseL2` 模板 / `holderL` 取算子值 E），范数 ≤ 1，a.e. 作用，保实（SL2），`Section4/D01/LerayMultiplier.lean` |
| 074-D01-p2-sl4a-div | 已合并 | 09-13 1803Z | #75 | #75 | P2 子引理 SL4α：经典解的 `div ∂ₜu(t,·) = 0`（`∂ₜ` 与 `div` 交换 + `divergence`），以及 `∂ₜu(t,·)` 的零阶 datum 横截（`⟪ξ, Â(ξ)⟫ = 0` a.e.），`Section4/D01/DivergenceTime.lean` |
| 075-R42-correction-path | 已合并 | 09-13 1834Z | #79 | #79 | R42 子引理 1e-i：修正 `w_ε + U_ε`（时空光滑、空间紧支）的 datum 路径在时间上连续（`D01.contDiff_angularPath` + 时间截断 + L1 唯一性），从而 `u_ε = v + (w_ε+U_ε)` 的 `sobolev` 字段由 `reference.sobolev` + 可加性得到，`Section4/R42/CorrectionPath.lean` |
| 076-A04-sl3-pairing | 已合并 | 09-13 1824Z | #78 | #78 | A04 SL3 配对：`⟨Δ_datum, ·⟩ = -‖∇‖²`，经 `angularFrequencyDilation` 酉性 (`inner_map_map`) 与 066 的符号事实 (`mid_symbol_imaginary`, `mid_symbol_order_independent`)，`Section4/A04/LaplacianPairing.lean` |
| 077-SIMP-C01 | 已合并 | 09-13 1811Z | #76 | #76 | C01 四个已合模块的 simplifier+tester（陈述逐字不变；负向检查；conformance examples；CI 闭包） |
| 078-B02-unit-2-split | 已合并 | #80 | #80 | B02 单元 2 `annularSchwartz`（L）拆分起步：`|ξ|^{-s}·g` 在环上光滑紧支（SL1）、Schwartz 逆角 Fourier（SL2）、实值性（SL3）、组装到 `IsHomogeneousSliceDatum`（SL4）；`research/B02/U2_SPLIT.md` + `Section4/B02/AnnularSchwartz.lean` |
| 079-D01-p2-sl4-transverse | 已合并 | 09-13 1921Z | #85 | #85 | P2 SL4 Fourier 横向形式：无散 `SmoothL2Field` 的任一 (m+1) 阶 datum 满足 a.e. `∑ⱼ ξⱼ Âⱼ(ξ) = 0`（经 066 `isSobolevDatum_partialDeriv` + 标量 datum 唯一性 + 符号消去），再推论到 `∂ₜu(t,·)`（D2 + 074 SL4α + `A05.SmoothL2` 包装），`Section4/D01/Transverse.lean` |
| 080-R42-blowup-esssup | 已合并 | 09-13 1851Z | #81 | #81 | R42 子项 2a：逐点 `SpeedUnboundedAt T u` + 切片连续 ⇒ `limsupLeft T (speedENorm (u(t,·))) = ⊤`（开集正测度 ⇒ essSup 下界；limsup=⊤ 的 frequently 刻画），`Section4/R42/BlowupEssSup.lean` |
| 081-D01-p2-leray-datum | 已合并 | 09-13 1902Z | #82 | #82 | P2 SL3 收尾：把 073 的 `lerayComplementL2` 重打包成 datum 载体上的 `lerayComplement m : RealVectorSobolev m →L[ℝ] RealVectorSobolev m`（`coordinates ∘ lerayComplementL2 ∘ assemble` + `codRestrict` 到实子空间），范数 ≤ 1、幂等、a.e. 作用、横向为零，`Section4/D01/LerayDatum.lean` |
| 082-A04-sl3-real-pairing | 已合并 | 09-13 1908Z | #84 | #84 | A04 SL3 步骤 3a：实载体 `RealSobolevHilbert` 上的反自伴 `⟪f, D_a g⟫_ℝ = -⟪D_a f, g⟫_ℝ`（`angularDirectionalDerivativeReal`，实 `L2.inner_def`）、降阶配对 `⟪Λ⁻¹w, Λw⟫ = ‖w‖²`、降阶符号只依赖 r−s，`Section4/A04/RealPairing.lean` |
| 083-R42-pressure-gradient | 已合并 | 09-13 1906Z | #83 | #83 | R42 子项 1f：`∇p_ε = ∇π + ∇P_ε ∈ L²`（参考压力梯度 L² + 修正压力空间紧支光滑 ⇒ 梯度 L²，`MemLp.add`），`Section4/R42/PressureGradient.lean` |
| 084-B02-unit-2-sl3 | 已合并 | 09-13 1930Z | #86 | #86 | B02 单元 2 SL3（M）：由 datum 的共轭反射对称得 `angularFourier (postcompCLM ofRealCLM (ψ i)) =ᵐ G i`（`ψ i` = `φ i` 的实部），加 SL4a（slice distribution）与 SL4b（可积性），`Section4/B02/AnnularReal.lean` |
| 085-D01-p2-sl7c-commute | 已合并 | 09-13 1951Z | #89 | #89 | P2 SL7c：`lerayComplement` 与降阶 `lowerDatum` 交换（复符号 0-齐次 + 与 `angularFrequencyDilation` 交换 + 标量权交换），推论：各阶 datum 的 Leray 补由 0 阶决定，`Section4/D01/LerayLowering.lean` |
| 086-SIMP-A04 | 已合并 | 09-13 1932Z | #87 | #87 | A04 八个较早合入模块（Forcing, Continuity, Gronwall, Regularized, DerivNorm, HighEnergy, TimeDerivative, MomentumDatum）的 simplifier+tester（陈述逐字不变；负向检查用 `set_option autoImplicit false`；conformance；CI 闭包） |
| 087-R42-sol-on-shorter | 已合并 | 09-13 1939Z | #88 | #88 | R42 装配子引理 #1 `sol_on_shorter`：由 `InsertionFamilyAPI` 在每个 `0<S<T` 上构造 `ClassicalSolutionR ν a (g_ε) S`（区间收缩 + 075 `CorrectionPath` + 083 `PressureGradient` + 080 切片连续），`Section4/R42/SolutionOnShorter.lean` |
| 088-A04-sl3-assembly | 已合并 | 09-13 2024Z | #94 | #94 | A04 SL3 步骤 3b（M）：Laplace datum 组装 `datum_m(Δu) = ∑ⱼ D_j D_j datum_{m+2}u` + 实反自伴 + 降阶配对 ⇒ `hlap : ⟪G, L⟫ ≤ -grad²`（`A04.inner_energy_assembly` 的输入），`Section4/A04/LaplacianAssembly.lean` |
| 089-D01-p2-sl5-longitudinal | 已合并 | 09-13 2014Z | #91 | #91 | P2 SL5：无旋（curl-free）光滑 L² 场的任一 datum a.e. 纵向 `ξᵢ Âⱼ = ξⱼ Âᵢ` ⇒ `Â(ξ) ∈ ℂ∙ξ`（镜像 079），再 datum 层 `lerayComplement m A = A`（081 review 的 4 行），`Section4/D01/Longitudinal.lean` |
| 090-SIMP-B02 | 已合并 | 09-13 2019Z | #92 | #92 | B02 七个已合模块（LowFrequency, Annular, LowHigh, Cutoff, LebesgueDatum, AnnularSchwartz, AnnularReal）的 simplifier+tester（陈述逐字不变；负向检查 autoImplicit off；conformance；MAINT 清单：a.e. 共轭模式去重、`angularFourier_conj`/`angular_plancherel`/`angularFrequencyDilation_coeFn` 上提） |
| 091-C01-partial-contract | 已合并 | 09-13 2010Z | #90 | #90 | 注册 `C01.energy_absorption_partial`：已证的 C01 spec 字段（velocityJets, forceTimeRegularity, trilinearHolder, trilinearAbsorbed, laplacianSqENorm）逐字进 `Contracts/V1/EnergyAbsorptionPartial.lean` + Bindings + Tests + contracts.json（模板 071 `B01.bochner_partial`），把 C01 模块纳入 CI 闭包 |
| 092-R42-lifespan-binding | 已合并 | 09-13 2020Z | #93 | #93 | R42 寿命两子句的绑定层装配（`verification/Bindings/InsertionLifespan.lean`）：由 `InsertionFamilyAPI` + `hg : MemForceR g` + `RegularThrough ν a g (T+δ)` 得 `maximalLifespanR ν a g_ε = ofReal T` 与 `ofReal (T+δ) < maximalLifespanR ν a g`（087 + 080 + 072 + `A02.maximal_partial`），为 V2 合同铺路 |
| 093-A01-split | 已合并 | 09-13 2107Z | #98 | #98 | A01（局部理论）拆分起步：对照 `research/A01/Spec.lean` 与 HeliCorgi 的 mild 存在/唯一/续接 API，写子引理表，证第一个 S 项（把 HeliCorgi 的局部解包装成 `A02.ClassicalSolutionR` 所需字段的桥），`research/A01/A01_SPLIT.md` |
| 094-D01-p2-sl7b-order0 | 已合并 | 09-13 2159Z | #105 | #105 | P2 SL7b-α：光滑 L² 场（不要求导数可积）的 0 阶 datum 的 a.e. 符号恒等式——无散 ⇒ 横向、无旋 ⇒ 纵向（分布导数 + `physicalDistribution_directionalField` + `OrderZeroDatum`），`Section4/D01/OrderZeroSymbol.lean` |
| 095-A04-sl5-nonlinear | 已合并 | 09-13 2056Z | #97 | #97 | A04 G1 SL5：非线性项的 H^m 分部积分 `⟪G, datum((u·∇)u)⟫ = -⟪∇G, datum(u⊗u)⟫`（实反自伴 082 + `derivDatumStep` 088）+ Cauchy–Schwarz ⇒ `hnl : -⟪G, N⟫ ≤ NLbound`（`A04.inner_energy_assembly` 的输入），`Section4/A04/NonlinearPairing.lean` |
| 096-R42-lifespan-contract | 已合并 | 09-13 2049Z | #95 | #95 | 注册 `R42.insertion_lifespan`（V1 新合同，含 `family`、`memForce`、`regular` + 两条寿命子句；Bindings 用 092 的 `insertionLifespan`；Tests 公理审计 + 两条论文显示式 example + `hν`/`ha` 可导出 example），把 `Bindings/InsertionLifespan` 纳入 CI 闭包 |
| 097-B02-remaining-fields | 已合并 | 09-13 2051Z | #96 | #96 | B02 剩余 spec 字段：`chi_*`（vendor `baseCutoff`，同 B01 绑定）、`temporalApprox`/`separatedAssembly`（B01 已证、逐字复用）、`annularPathApprox`（路径级截断，M）、`approxCompactHomogeneous`（stage 1–5 组装）；先表后证 S 项，`Section4/B02/Remaining.lean` + `research/B02/REMAINING_SPLIT.md` |
| 098-R42-full-horizon | 已合并 | 09-13 2126Z | #100 | #100 | R42 导出：由每个 `Ico 0 S`（S<T）上的 datum 路径经唯一性粘成 `Ico 0 T` 上的连续路径（S–M），从而 `ClassicalSolutionR ν a g_ε T`（水平线恰为 T）；A02 `IsMaximalSolution`/`insertion_lifespan_eq` 半边的表，`Section4/R42/FullHorizon.lean` |
| 099-B02-partial-contract | 已合并 | 09-13 2125Z | #99 | #99 | 注册 `B02.homogeneous_partial`：16 个已证字段（含带可积性形式的 `homogeneousDatumSub` + 反例注释）逐字进 `Contracts/V1/HomogeneousPartial.lean` + Bindings + Tests + contracts.json（模板 071/091），把 B02 八个模块纳入 CI 闭包；缺 `separatedAssembly`/`annularPathApprox`/`approxCompactHomogeneous` |
| 100-A04-sl5a-divergence-form | 已合并 | 09-13 2141Z | #102 | #102 | A04 SL5 行 5a（M）：无散场的对流项散度形式 `advection u t x = ∑ⱼ partialDeriv j (fun y => u (t,y) j • u (t,y)) x`（Leibniz + `spatialDivergence = 0`），`Section4/A04/AdvectionDivergence.lean` |
| 101-A01-p1-potential | 已合并 | 09-13 2153Z | #103 | #103 | A01 单元 P1（M，无依赖无 gap）：径向势 `pressurePotential G` 在 `HasSymmetricJacobian G` 下梯度为 `G`（`02-preliminaries.tex:96-100`；`intervalIntegral` 下求导 + FTC），同时结掉 `pressure_potential`(m4) 与 D01 L9(b)，`Section4/A01/RadialPotential.lean` |
| 102-A04-sl5-columns-norms | 已合并 | 09-13 2134Z | #101 | #101 | A04 SL5 行 5b/5f/5g（均 S）：列 `W_j = u_j • u` 的 m+1 阶 datum（`tameProductVector`/`outerProductTame`）；`√(∑‖D_j G'‖²) = gradientSobolevNormAt`；`√(∑‖B_j‖²) ≤ (outerSobolevENorm …).toReal`，`Section4/A04/NonlinearColumns.lean` |
| 103-B02-separated-assembly | 已合并 | 09-13 2206Z | #106 | #106 | B02 `separatedAssembly`（M）：分离和 `∑ φ_j(t) h_j(x)` 的齐次 datum 路径，经 reviewer 给的短路线（`isHomogeneousSliceDatum_unique` + `isHomogeneousPath_compact` + `homogeneousVectorDatum` 线性性，`-3/2<s`），`Section4/B02/SeparatedAssembly.lean` |
| 104-SIMP-D01 | 已合并 | 09-13 2156Z | #104 | #104 | D01 较早合入的八个模块（ForceClass, SmoothDatum, DatumToJets, HalfOrder, Pressure, HomogeneousWitness, OrderZeroDatum, LeraySymbol）的 simplifier+tester（陈述逐字不变；负向检查 autoImplicit off；conformance；MAINT 清单） |
| 105-A04-sl5c-column-data | 已合并 | 09-13 2222Z | #108 | #108 | A04 SL5 行 5c（M）：每列 `W_j = u_j • u` 的 `SmoothL2Field` 包装（Leibniz + L^∞ 因子）+ `N = ∑ⱼ derivDatumStep m j (castOrder … B_j)`（`isSobolevDatum_partialDeriv` 一次 + `isSobolevDatum_add` + 唯一性），`Section4/A04/NonlinearDatum.lean` |
| 106-A01-m4-gauge | 已合并 | 09-13 2225Z | #109 | #109 | A01 字段 `pressure_potential`（m4）的规范包装：`PressureGaugeEquivOn (Ico 0 T)` 于 `p` 与 `pressurePotential (∇p)`（`is_const_of_fderiv_eq_zero` + 切片 fderiv 引理 + Hessian 对称 `ContDiffAt.isSymmSndFDerivAt`），reviewer 已写 52 行，`Section4/A01/PressureGauge.lean` |
| 107-SIMP-R42 | 已合并 | 09-13 2220Z | #107 | #107 | R42 已合模块（Assembly, Lifespan, CorrectionPath, PressureGradient, BlowupEssSup, SolutionOnShorter, FullHorizon）的 simplifier+tester（陈述逐字不变；负向检查 autoImplicit off；conformance；`Bindings/InsertionLifespan` 闭包必须保持绿） |
| 108-D01-p2-sl7b-curl | 已合并 | 09-13 2252Z | #110 | — | P2 SL7b-β：把 094 的截断配对机器推广为常数权重矩阵 `physical_weighted_pairing_zero`，得 0 阶 datum 的无旋 ⇒ 纵向（`OrderZeroSymbol` 上 Lemma B，reviewer 估 ≈30–40 行），推论 `lerayComplement 0 (orderZeroDatum hz) = orderZeroDatum hz`，`Section4/D01/OrderZeroCurl.lean` |
| 109-MAINT-promotions | 已合并 | 09-13 2258Z | #112 | — | MAINT：把各 reviewer 标记的 Paper3/Source 级事实上提（`angularFrequencyDilation_coeFn`+`transverse_of_transverse_symm`→Paper3，`angular_plancherel`→Paper3，`angularFourier_conj`→Source/FourierConvention，A04 datum 线性引理→A03，`columnsSobolevENorm_toReal_sq_eq_sum`→A03），旧位置留 alias，陈述逐字不变，`make test` 18/18 |
| 110-B02-approx-compact | 已合并 | 09-13 2315Z | #113 | — | B02 结论字段 `approxCompactHomogeneous`（M，90–140 行）：跨 realization 的三角不等式粘合 `bochnerDatumENorm q s (separatedPath φ A − separatedPath φ A') ≤ ∑ ‖φ_j‖_{L^q}·‖A_j − A'_j‖ₑ` + `temporalApprox` + `spatialApproxHomogeneous` + `separatedAssembly`（103），`Section4/B02/ApproxCompact.lean` |
| 111-D01-p2-sl8-prep | 已合并 | 09-13 2320Z | #114 | — | P2 SL8 预备：`orderZeroDatum` 可加性/线性（唯一性）、`∂ₜu(t,·)` 与 `∇p(t,·)` 的 `MemLp 2` 与 `ContDiff`（`∂ₜu = h − ∇p`，`h ∈ H^∞`）、0 阶 `(I−P) datum⁰(h) = datum⁰(∇p)` 的表（等 108 的纵向引理）与 bootstrap 路线（085 `isSobolevDatum_lower_iff`），`Section4/D01/OrderZeroAlgebra.lean` + `research/D01/SL8_SPLIT.md` |
| 112-A01-regularity-partial | 已合并 | 09-13 2256Z | #111 | — | A01 部分合同 `A01.regularity_partial`：`ManuscriptLocalRegularity` 已证的两个字段 `projected`（093）与 `pressure_potential`（106）逐字进 `Contracts/V1/RegularityPartial.lean` + Bindings（含 `pressurePotential`/`HasSymmetricJacobian` 的 `rfl` 桥）+ Tests + contracts.json（模板 091/099） |
| 113-SIMP-A01 | 已合并 | 09-13 2351Z | #117 | — | A01 已合入的四个模块（ConvectionDivergence, ProjectedEquation, RadialPotential, PressureGauge）的 simplifier+tester（陈述逐字不变；负向检查 autoImplicit off；conformance 重跑 axioms_a01/p1/m4；MAINT 清单） |
| 114-R42-lifespan-v2 | 已合并 | 09-13 2329Z | #115 | — | R42 `insertion_lifespan` **V2** 合同：`extends` V1 + 098 已证的 `solution`（`u_ε,p_ε` 是 `ClassicalSolutionR ν a g_ε T`，导出 `sobolev`/`pressure_gradient`）+ `maximal`（`Contracts.V2.MaximalPartial.IsMaximalSolution`）+ 论文 04:34 第二显示式 `limsup` 形（`limsupLeft_speedENorm_eq_top`）；补 REVIEW_CONTRACT.md 列的三个欠项 |
| 115-SIMP-A04 | 已合并 | 09-14 0012Z | #119 | — | A04 SL3 簇四个模块（LaplacianDatum, LaplacianPairing, RealPairing, LaplacianAssembly；086 未覆盖）的 simplifier+tester（陈述逐字不变；负向检查 autoImplicit off；重跑 axioms_sl3*；MAINT 清单）。SL5 簇五个 Nonlinear* 模块另开 |
| 116-B02-homogeneous-v2 | 已合并 | 09-13 2350Z | #116 | — | B02 `homogeneous_partial` **V2** 合同：`extends` V1 + `separatedAssembly`（在 `−3/2<s` 上，103）+ `approxCompactHomogeneous`（110，`SplitRange`）；`annularPathApprox` 仍排除（无证明、无消费者）；Bindings/Tests/contracts.json（第 20/21 条） |
| 117-D01-p2-sl8-assembly | 已合并 | 09-13 2356Z | #118 | — | **P2 SL8 组装**（S，≈55 行，reviewer 探针已编译）：`D01/PressureJets.lean`，0 阶恒等式 `datum⁰(∇p) = (I−P)₀ datum⁰(h)`（094 横向 + 108 纵向 + 111 代数）→ 085 `isSobolevDatum_lower_iff` 逐阶提升 → `SmoothSquareIntegrableJets (∇p(t,·))`；即 P2 = eq:Rpressure 的 Lean 定理 |
| 118-SIMP-A04-nonlinear | 已合并 | 09-14 0021Z | #120 | — | A04 SL5 簇五个模块（AdvectionDivergence, NonlinearPairing, NonlinearColumns, NonlinearDatum, NonlinearBound；100/102/105）的 simplifier+tester（陈述逐字不变；真负向检查；重跑 axioms_sl5*；MAINT 清单） |
| 119-A01-c1b-split | 已合并 | 09-14 0033Z | #121 | — | A01 L 单元 **C1b** 拆分起步：D01 角向 datum `IsSobolevDatum m` ⟷ Euler `ordinarySobolev`/`EulerMeanSolenoidal.L2` 坐标（经 cylinder `ordinaryLift` 伴随）逐阶桥；产出 `research/A01/C1B_SPLIT.md`（S/M 子引理表 + file:line 输入）+ 证第一个 S 单元 |
| 120-D01-p2-contract-v3 | 已合并 | 09-14 0038Z | #122 | — | **P2 合同**：`D01.datum_lemmas` V3（`Contracts/V3/DatumLemmas.lean` extends V2）三字段 `solution_slice_pressureGradient_smoothJets` / `…_temporalDerivative_smoothJets` / `…_pressureGradient_exists_datum`（A04 `hP` 形）+ `Bindings.DatumLemmasV3`（经 `uniqueness_toA02`）+ Tests + contracts.json（第 22 条）；照 `REVIEW_SL8_ASSEMBLY.md` §6/附录 C |
| 121-A04-hpr-leray-adjoint | 已合并 | 09-14 0048Z | #124 | — | A04 eq:Rhigh 最后一块 **`hpr : ⟪G,P⟫ = 0`**（S–M）：`lerayComplement s` 在 `RealVectorSobolev s` 上自伴（符号 `ξξᵀ/‖ξ‖²` 实对称投影，062）；`(I−P)ₘ G = 0` 对无散速度切片的 order-m datum（0 阶横向 094 + 085 lowering，同 117 的 bootstrap）；配合 117 的 `pin_pressureGradient_datum` 得 `⟪G,(I−P)ₘ Am⟫ = 0` 即 `HighEnergy.lean:105` 的 `hpr` |
| 122-A01-a3-split | 已合并 | 09-14 0054Z | #126 | — | A01 L 单元 **A2/A2b/A3** 拆分起步（高阶传播 eq:Rhigh 的 A01 用法、order-m 续接、阶无关 T₀）：对照 A04 已有的 `Gronwall`/`HighEnergy`/`TimeDerivative`/`Continuity`/`Regularized` 与 OpenAI `Source/OrdinaryForced*`，产出 `research/A01/A3_SPLIT.md` + 证第一个 S 单元 |
| 123-MAINT-pairing-home | 已合并 | 09-14 0046Z | #123 | — | MAINT：把 `A04/LaplacianPairing.lean`、`A04/RealPairing.lean`（内容全在 `namespace Paper3`，不用任何 A04 声明）搬到与其 import 相符的最低层（Paper3/ 或 D01/），消除 `D01/LerayLowering` → A04 的反向边（115 审稿）；更新所有 importer 与 conformance 文件；陈述逐字不变 |
| 124-A01-c1b-c8-0 | 已合并 | 09-14 0122Z | #128 | — | A01 C1b 行 **C1b-c8-0**（M）：0 阶 datum 路径连续性 `Continuous U → Continuous (fun t => orderZeroDatum (Lp.memLp (U t)))`（`orderZeroDatum` 作为 `L²` 参数的 CLM 复合）；喂 `ClassicalSolutionR.sobolev` 的 `m=0` 情形 |
| 125-D01-finite-order-datum | 已合并 | 09-14 0132Z | #129 | — | D01 有限阶 datum 构造子（C1b 真正的阻塞 C1b-m-D，M–L，拆分起步）：`MemLp z 2` + 各阶 ≤ m 的 L² 弱导数 ⇒ `∃ A, IsSobolevDatum m z A`（D01 目前只有 0 阶 `orderZeroDatum` 与全阶 `smoothAngularDatum`）；产出 `research/D01/FINITE_ORDER_SPLIT.md` + 证第一个 S 单元 |
| 126-A01-a2b-continuation | 已合并 | 09-14 0146Z | #131 | — | A01 A2b-a′（122 审稿改判：OpenAI 层有续接判据）：`Section4/A01/Continuation.lean`，S 步 `forced_global_mild_of_bound`（`Euler/BoundedMildContinuation.lean:39` 喂 `ForcedCylinderLocal.coefficients`），M 步补回无散与角不变两子句并降到 `C(Icc 0 S, EulerMeanSolenoidal.L2)`（照 `exists_local` 尾部） |
| 127-MAINT-hotfix-pressuredrop-import | 已合并 | 09-14 0049Z | #125 | — | 热修：#124（121）在 #123（搬 RealPairing 到 D01）之后合入，`A04/PressureDrop.lean` 仍 `import …A04.RealPairing`，integration 门禁红（wave80 exit=2）；改一行 import 为 `D01.RealPairing`（lead 手改，一行） |
| 128-A04-energy-identity-high | 已合并 | 09-14 0116Z | #127 | — | **A04 eq:Rhigh 组装**（S，121 审稿探针已编译）：`Section4/A04/EnergyIdentityHigh.lean`，`def Chigh m := A03.outerTameConst m` + `Chigh_pos`，`energyIdentityHigh` 逐字取 `research/A04/Spec.lean:424-434` 的 ∀ 前缀形；顺手修 121 两个 probe 的旧 import |
| 129-SIMP-D01-orderzero | 已合并 | 09-14 0148Z | #132 | — | D01 P2 链五个模块（OrderZeroSymbol 094, OrderZeroCurl 108, OrderZeroAlgebra 111, MomentumSlice 111, PressureJets 117）的 simplifier+tester（陈述逐字不变；真负例/反例；重跑 axioms_order_zero*/sl8*；MAINT 清单：108 四处重复、111 死代码 `lerayComplement_orderZeroDatum_add/_sub`、与 121 的横向论证重复） |
| 130-SPEC-A04-rhigh-blind | 已合并 | 09-14 0141Z | #130 | — | 硬规矩 2：eq:Rhigh 的盲写双稿（两个只读论文 + 合同词汇、互不可见的 agent 各写一版 `research/A04/blind/rhigh_{A,B}.lean`），再由 comparer 与 128 的 `energyIdentityHigh` 三方比对，差异写进 `research/A04/BLIND_RHIGH.md`；A04 合同冻结前必做 |
| 131-C01-energy-split | 已合并 | 09-14 0205Z | #133 | — | C01 剩余能量/涡量字段拆分起步（`energyIdentity`/`energyDifferentialBound`/`l2Bound`、`enstrophyIdentity` 等，Spec.lean:344-541）：对照 A04 已有的 `inner_energy_assembly`/`TimeDerivative`/`Continuity` 与 121 的 `pressure_drop`（m=0/1 实例），产出 `research/C01/ENERGY_SPLIT.md` + 证第一个 S 单元 |
| 132-D01-db-transport | 已合并 | 09-14 0228Z | #137 | — | D01 行 **D-b-transport**（M，≈50 行）：把 125 审稿在 cycles 变量下证出的弱导数乘子恒等式搬到角向原变量（`memLp_coord_smul_datum`，模板 `Transverse.lean:177-205`），然后 **D-close**：从 `orderZeroDatum` 对 m 归纳、经 `raisableWitness_of_memLp_smul` + `isSobolevDatum_raise` 得 `exists_isSobolevDatum_of_memLp_derivs`（收掉 C1b-m-D） |
| 133-A04-energy-high-contract | 已合并 | 09-14 0211Z | #134 | — | **A04 首个合同** `A04.energy_high_partial`：`Contracts/V1/EnergyHighPartial.lean`（`Chigh` 不透明 + `Chigh_pos` + `energyIdentityHigh` 逐字取树形；重述 `sobolevNormAt`/`gradientSobolevNormAt`/`HasSmoothSobolevPath` 各配 rfl 桥）+ Bindings（经 `uniqueness_toA02`）+ Tests + contracts.json（第 23 条）；scope 按 `BLIND_RHIGH.md` §5 披露；顺手把 `gradientSobolevENorm_velocity_ne_top` 收进树 |
| 134-A01-a2b-invariance | 已合并 | 09-14 0223Z | #135 | — | A01 行 **A2b-b**（M，≈150–190 行）：带角不变性的续接——每个窗口在 `kernelMass δ·L<1` 唯一性区间内（126 审稿探针 `probe_window_invariance`/`probe_restart_window_invariance`），做 invariance-carrying restart（≈80）+ `gluePath_invariant`（≈10）+ fork vendor 的 45 行归纳（≈60），从而无条件得到 `forced_global_of_bound` 的 `hinv` |
| 135-A04-g2-highcontinuation | 已合并 | 09-14 0223Z | #136 | — | A04 G2：eq:highcontinuation（`appendix-a-local-theory.tex:139-145`）——由 128 的 `energyIdentityHigh` 经 Young + ζ 正则化除法（`Regularized.lean` 的 `sqrt_le_primitive_linear`/`regularized_sqrt_deriv`）得 `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}`，逐字取 Spec 字段 |
| 136-C01-e2-vocabulary | 已合并 | 09-14 0301Z | #139 | — | C01 行 **E2 词汇桥**（S–M，≈60–90 行）：spec 的 `l2Sq`/`gradientSq`/`pairing`（`slice`）与载体 B 的 `field_inner`/`PiLp.norm_sq_eq_of_L2`/`laplacian_pairing` 平方和之间的三条恒等式 + `Real.sqrt` 适配器，喂 131 的 `inner_energy_identity` |
| 137-A01-a3-force-cap | 已合并 | 09-14 0305Z | #140 | — | A01 A3 行 **A3-L1·f**（S）：力的一致积分帽 `∫₀ᵗ ‖f(s)‖_{H^m} ds ≤ Bbnd` 对 `t ∈ [0,T₀)`（由 `MemForceR` 经 `Continuity.lean` 的 `continuousOn_sobolevNormAt_force` + 区间可积得到），喂 122 的 `gronwall_bddAbove_Ico` 的 `Bbnd` 槽；顺带 `0 ≤ y_m 0` 无需桥的说明 |
| 138-A04-g2b-integral | 已合并 | 09-14 0258Z | #138 | — | A04 **G2b** `highContinuationIntegral`（`Spec.lean:471-494`，S）：ζ↓0 的积分式 eq:highcontinuation —— 135 的 `deriv_normSq_absorbed_deriv` + `Regularized.lean` 的 `sqrt_le_primitive_linear`（E=‖u‖²_{H^m}, K=Cgron·‖u‖²_{H²}, b=‖f‖_{H^m}）+ `Continuity.lean` 的 `intervalIntegrable_highContinuationIntegrand`（显式传 `A04.Cgron`）；逐字取 spec 字段；之后 A04 V2 合同一批注册 |
| 139-A01-a3-l2-horizon | 已合并 | 09-14 0349Z | #142 | — | A01 A3 行 **A3-L2**（S，无依赖）：`horizon := S`——用 134 的 `forced_global_of_bound_unconditional` 在给定先验界下定义并证明 A01 在指定 `[0,S]` 上的局部理论输出（`LocalTheoryAPI.horizon`/`solution` 的 `hbound` 条件形），不再对 `exists_local` 的 `∃ T` 做选择 |
| 140-A01-euler-pairing | 已合并 | 09-14 0409Z | #144 | — | C1b 行 **D-euler-pairing / C1b-m-E**（M）：Euler 侧把柱面导数 word（`word_hasDerivAt`/`word_has_jet`/`ofJet` + `exists_ordinary_value`）降成 L² 场并证 Schwartz 配对形 `∫ψ·(∂ⱼz)ᵢ = ∫(−∂ⱼψ)·zᵢ`（132 审稿的 E1 记账 ≈60–90 行 + E2 平移不变性 ≈40–120 行），产出 `HasWeakDerivsL2 (⇑(U t)) m`（m ≤ q−2），从而 132 的 `exists_isSobolevDatum_of_memLp_derivs` 在速度上点火；解锁 A3-L1·k 与 C1b-c8-m |
| 141-A04-energy-high-v2 | 已合并 | 09-14 0335Z | #141 | — | **A04 V2 合同** `A04.energy_high_partial_v2`：`Contracts/V2/EnergyHighPartial.lean` extends V1，新增 `Cgron`（不透明）/`Cgron_pos`/`regularizedNormDerivative`（G2，诚实孤儿：G2b 不经过它）/`highContinuationIntegral`（G2b）；仅新增重述 `MemL1Hm` + 第四条 rfl 桥；scope 十条披露（138 审稿）；Bindings 里 `Cgron = Chigh²/(4ν)` 作 rfl bonus |
| 142-A01-a3-m2-gronwall | 已合并 | 09-14 0349Z | #143 | — | A01 A3 行 **A3-M2**（S，胶水）：在 `ClassicalSolutionR` 上实例化 122 的 `gronwall_bddAbove_Ico`——`hstep` ← 138 的 `highContinuationIntegral` 在 `t₀ := 0`；`hy0` ← 137 的 `sobolevNormAt_nonneg`；`hy`/`hk` ← `continuousOn_sobolevNormAt_velocity`；`hb`/`hbnn`/`hbbnd` ← 137 的 `forceCap`；`hCgron` ← `Cgron_pos`；唯一留空 `hkbnd`（`Kbnd = ∫₀^{T₀}‖u‖²_{H²}` 上界，A3-L1·k）作为显式假设 |
| 143-C01-e3-e4-momentum | 已合并 | 09-14 0530Z | #146 | — | C01 行 **Ep/E3/E4**（S + S–M + M≈120 行）：载体 B 上为 `ClassicalSolutionR` 交付 `energyIdentity` 装配还欠的三件事——∇p 打包（P2）、动量分裂推到 `Lp`（由 `ClassicalSolutionR.momentum`）、`t ↦ ‖u(t)‖²₂` 的 `HasDerivAt`（`wordEnergy_hasDerivWithinAt` + `Evolution.velocityField_jetLp_continuous` + ∂ₜu 路径的 jetLp 连续性）；之后 Bindings 侧 ≈30 行进 C01 V2 |
| 144-MAINT-zero-solution | 已合并 | 09-14 0518Z | #145 | — | MAINT：把零解见证落地一次（`Section4/A04/ZeroSolution.lean`：`zeroSol : ClassicalSolutionR ν 0 0 T`、`memForceR_zero`、`zero_mem_initialClassR`、`HasSmoothSobolevPath` 见证、`sobolevNormAt_zero`），八次审稿各自重建；之后各 axioms_*.lean 可 import 它 |
| 145-D01-quantitative-constructor | 已合并 | 09-14 0556Z | #147 | — | D01 **A3-L1·k-quant**（M，≈120–200 行，无外部输入）：给 132 的 `exists_isSobolevDatum_of_memLp_derivs` 补定量版——沿归纳跟踪范数 `‖A‖² ≤ c_m · Σ_{α, 阶≤m} ‖∂^α z‖²_{L²}`（119 曾 disclaim 的带 m 依赖常数的范数比较）；配 140 的 `‖word‖ ≤ ‖u‖`、`‖ordinaryLift Zw‖ = ‖Zw‖` 一行事实，即得 `sobolevNormAt 2 (⇑U t) ≤ c·(‖u₀‖+1)`，从而 `Kbnd`；`exists_local` 到 `Kbnd` 之间唯一剩下的东西 |
| 146-C01-jet-paths | 已合并 | 09-14 0601Z | #148 | — | C01 **E4 路线 (a) 的 S 半：喷流连续路径**（S–M，≈100 行）：对 ClassicalSolutionR 在 Icc 0 S（S<T）上建 SmoothL2Field 路径并证 ∀ n 的 jetLp 连续——力路径（MemForceR 的 ContDiffOn G 镜像 velocityField_jetLp_continuous）、Δu 与 ν•Δu（continuous_jetLp_directionalField + addField/mapField）、(u·∇)u（vendor SmoothEulerEvolution.lean:29 实例化）、动量残差 h = f − (u·∇)u + νΔu；记录 ∇p = lerayComplement h 还差的 datum/喷流双向连续桥（与 145 的定量构造子共用） |
| 147-A01-a3-l1k-glue | 已合并 | 09-14 0638Z | #149 | — | A01 **A3-L1·k 胶水**（S–M，≈80–120 行）：lane 140 hasWeakDerivsL2_of_cylinder 的定量孪生（HasWeakDerivsL2Bound (⇑(U t)) ‖u t‖² 2，常数 1：‖word 1 u hn w‖ ≤ ‖u‖ + ordinaryLift 线性等距），配 145 的 256 与 A04.Forcing.sobolevENorm_eq 得 sobolevNormAt 2 (⇑(U t)) ≤ 16·‖u t‖（q ≥ 4），再由 ‖u‖ ≤ ‖u₀‖+1 得 Kbnd；照 research/D01/probes/rev145_a3l1k_glue.lean |
| 148-C01-e4b-pressure-jets | 已合并 | 09-14 0702Z | #150 | — | C01 **E4b**（M，≈120–180 行）：喷流 ⇒ order-m datum 路径连续（145 的 ‖A‖² ≤ 16^m·M 给范数控制，需喷流与坐标弱导数的桥）→ 动量残差 datum 路径连续 → lerayComplement（CLM）→ ∇p datum 路径连续 → jetOfDatum_continuous 得 ∇p 喷流连续 → ∂ₜu 的 hB → wordEnergy_hasDerivWithinAt 得 E4；146 的 residualPath 为输入 |
| 149-A01-a3-widen-converse | 已合并 | 09-14 0741Z | #151 | — | A01 **A3 残留行 (iii)+(ii)**（S + M）：(iii) T₀ < T 情形的 Ico → Icc 端点加宽（T₀ ∈ Ico 0 T，continuousOn_sobolevNormAt_velocity 现成，纯区间/连续性记账）；(ii) 反向范数比较 ∃ C 与 t 无关，‖u t‖_{SobolevSpace 1 (q+1)} ≤ C · sobolevNormAt (q+1) (⇑(U t))（147 正向 16‖u‖ 的反面；注意阶不对称）；照 research/A01/REVIEW_ORDER_TWO_CAP.md 残留行审计 |
| 150-C01-e4-assembly | 已合并 | 09-14 0818Z | #152 | — | C01 **E4 装配**（M，≈120–180 行）：energyDerivative_hasDerivAt——把 143/146/148 的路径平移到 vendor 的 Icc 0 T'（T' := S − c），hA = velocityField_jetLp_continuous，hB = temporalSlicePath_jetLp_continuous，逐点 hd 从 velocity_smooth 重证（树里未导出），s=0 词桥（wordField_zero + 单点 Fin 0 → Fin 3，vendor 无 wordEnergy_zero），HasDerivWithinAt → HasDerivAt；接 energyIdentity_classical 得 C01 energyIdentity 对 ClassicalSolutionR 无条件；精确陈述见 research/C01/REVIEW_E4B.md §4 |
| 151-A01-carrier-words | 已合并 | 09-14 0850Z | #153 | — | A01 **载体桥子引理 (a)(b)(c)**（S–M，≈120 行）：(a) word_descent_ae_partial——下降到经典喷流的 a.e. 恒等（n + 3 ≤ q + 1，空间词，光滑代表元 z）；(b) eLpNorm_jet_component_le（多线性算子范数在单位向量上）；(c) word_angular_eq_zero（角不变下角向词为零，149 探针已证）；合成 hword_jet 于 n ≤ q − 2，使 149 的反向比较在低阶无条件；探 (d) 角不变 lift 的 L² 级 descent（Fubini，去掉 3 阶损失）——只记录形状与障碍；照 research/A01/REVIEW_APRIORI_ROWS.md §2 |
| 152-C01-v2-contract | 已合并 | 09-14 0852Z | #154 | — | C01 **V2 合同**（M，verification 侧）：formalization 前置（pairing def 逐 token 抄 Spec.lean:196；导出无截断 l2Sq 形式 rev150_gap.lean）→ Contracts/V2/EnergyAbsorptionPartial.lean（V1 六字段逐字 + gradientSq/pairing 两个 spec-local def + energyIdentity 字段逐 token 抄 Spec.lean:344-350）→ Bindings（uniqueness_toA02；rfl 桥抄 V1；唯一非 rfl 桥 gradientSq = PiLp.norm_sq_eq_of_L2）→ Tests → contracts.json 第 25 条（ensure_ascii=False）；照 research/C01/REVIEW_E4.md §4 |
| 153-A01-l2-descent | 已合并 | 09-14 0932Z | #155 | — | A01 载体桥 **(d) L² 级 descent**（M–L）：角不变的 lift g : LiftL2 1 是某 G : EulerMeanSolenoidal.L2 的 ordinaryLift（无喷流假设，去掉 exists_ordinary_value 的 3 阶损失）；路线：liftMeasure = volume.prod volume（EulerProof.lean:1092），AddCircle Fourier Hilbert 基（Mathlib/Analysis/Fourier/AddCircle.lean:411/261）杀掉非零模；配 151 得 hword_jet 顶三阶 n ∈ {q−1,q,q+1}；照 research/A01/probes/probe151_descent_L2.lean 与 REVIEW_CARRIER_WORDS.md |
| 154-C01-v3-bounds | 已合并 | 09-14 0932Z | #156 | — | C01 **V3 前置：energyDifferentialBound + l2Bound**（S–M）：由 V2 的 energyIdentity（HasDerivAt.unique + Cauchy–Schwarz + norm_toLp_sq_eq_l2Sq，136 审稿 finding 8）得 (‖u‖²)' ≤ 2‖u‖‖f‖（Spec.lean:364）；再由 Paper1.sqrt_energy_le_primitive 的推广得 eq:RL2 的 ‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f‖₂（Spec.lean:383）；formalization 侧模块 + 记录，V3 合同下一条 lane |
| 155-SIMP-d01-c01-dedup | 已合并 | 09-14 1211Z | #158 | — | SIMP/tester 通道：145 F3（coord_smul_deriv_ae 上提到 FiniteOrderConstructor 去重）、145 F2（新增锐等式 ‖raise A‖² = ‖A‖² + Σ‖Cⱼ‖² 与 4^m 构造子，16^m/256 陈述不动）、146 N1（continuous_jetLp_sumField/laplacianField_jetLp_continuous 与 Source/PhysicalBesselSobolev.lean:83,105 去重）、144 分层（isSobolevDatum_zero 下沉到 D01，ZeroSolution 去掉 PressureDrop import）、153 N3（退役 151 被 subsume 的三条）；全部依赖模块重编 + gates |
| 156-C01-v3-contract | 已合并 | 09-14 0955Z | #157 | — | C01 **V3 合同**：Contracts/V3/EnergyAbsorptionPartial.lean extends V2 + energyDifferentialBound + l2Bound（逐 token 抄 Spec.lean:364-370 / :383-387）+ forcePrimitive/energyBudget 两个 spec-local def；Bindings（V2 回投 rfl；l2Bound 无桥；energyDifferentialBound 用 V2 的 gradientSq 桥，154 审稿 dry run 已通）；Tests；contracts.json 第 26 条；照 research/C01/REVIEW_ENERGY_BOUNDS.md §3 |
| 157-A01-slice-wiring | 已合并 | 09-14 1214Z | #159 | — | A01 载体桥 **切片接线（S）+ hslice/horizon 匹配（M–L）**：把 149/153 的 Z : SmoothL2Field 与 hfin 接到真实 ClassicalSolutionR 速度切片（D01.exists_smoothL2Field_of_memHInfty + contDiff_slice + w.sobolev），得到对真实解的无条件反向比较；再把 exists_local_shape_of_aprioriBound 的 (u,U) 与 ClassicalSolutionR 的速度切片对齐（hslice : ∀ t, v(t,·) =ᵐ ⇑(U t)，horizon T 匹配）；照 research/A01/REVIEW_L2_DESCENT.md 缺口排序 1–3 |
| 158-A01-b1-constructor-split | 恢复完成；本地检查通过，PR 待审查 | 09-15 0659Z | — | #161 | `ConstructorPieces`：弱导数与候选切片 datum 扩至所有 `m ≤ q+1`，连续 ordinary L² derivative-word 路径；顶阶 datum/path、公理及完整前件消费探针通过。`CarrierConstructorFull` 仍是研究目标；联合光滑性、共同时间区间及初值/外力同定未闭合。 |
| 159-R43-split | 已合并 | 09-14 1246Z | #160 | — | R43 **命题 4.3 拆分**（research + 首个 S 行）：照 research/R43/COMPARISON.md §4 的 G1–G8 与 Spec.lean RCritical1API 四字段，写 research/R43/R43_SPLIT.md（每个上游缺口现状：A05.gradient_l6、A04 energy_high V2、C01 V3 已注册；G7 eq:Rcritical1 自有 L 步）；证 S 行（G6 ℕ-pow/rpow 拼写钉、G3 非空洞、G8 常数算术）于 Section4/R43/*.lean |
| 160-A04-restart-beyond | 由 owner PR #161 完成（restartBeyond 以 Restart 为假设；lifespan 以 HigherOrderBound 为假设） | 09-15 1254Z | — | — | A04 **R1 restartBeyond（M）+ C1 lifespanInfiniteOfLocallyFinite（S）**：R43 消费的寿命子句（159 审稿判为三条未证兄弟子句中最便宜）；以 A02 MaximalSolutionAPI.restart（依赖 A01 存在性 ⟪A01:solution⟫）为具名显式假设，证 A04 自有部分：t₀ ↑ S 极限与 δ 与 t₀/S 无关、maximalLifespanR 的 sup 记账（模板 FormalPatched/R3MildContinuation.lean:122）、C1 序论证（Source/SmoothLifespan）；照 research/A04/COMPARISON.md:216-217 |
| 161-A01-b1-time-ladder | 已合并 | 09-15 1859Z | #172 | — | A01 **B1 时间正则阶梯 rung 1**（HANDOFF P8）：datum 路径的连续 selection（R1）+ 阶梯表 B1_LADDER.md；任务书 collaboration/briefs/161-*.md |
| 162-A01-c6-divergence | 已合并 | 09-15 1901Z | #174 | — | A01 **c6 散度 a.e.**（HANDOFF P7a）：从柱面对的 divergenceFreeSpace 子句下降到光滑代表元的 Σ∂ᵢuᵢ = 0 a.e.，逐点升级以 c3 为具名假设 |
| 163-C01-e5-enstrophy | 已合并 | 09-15 1859Z | #173 | — | C01 **E5 enstrophy 导数**（HANDOFF P2 首环）：vendor wordEnergy_hasDerivWithinAt 在 s=1 减 s=0，分部积分得 −2⟪Δu,∂ₜu⟫，镜像 EnergyDerivative.lean |
| 164-D01-g1-homogeneous-norm | 已合并（第 27 条合同） | 09-15 1913Z | #176 | — | D01 **G1 dotHomogeneousENorm**（HANDOFF P4）：datum 形齐次 Ḣ^s 范数定义 + 基本引理 + Contracts/V2 重述与 rfl 桥 + 注册（第 27 条） |
| 165-A05-critical-l3 | 已合并 | 09-15 2025Z | #183 | — | A05 **velocityCriticalL3**（HANDOFF P3）：Riesz 路线（Paper1/SchwartzCriticalEmbedding）到 spec 词汇的载体翻译 U1–U7；不注册（等 164） |
| 166-R44-split | 已合并 | 09-15 1908Z | #175 | — | R44 **命题 4.4 拆分**（HANDOFF P6）：R44_SPLIT.md + Pieces.lean（拼写钉/常数算术/bootstrap 复用），注册审计 |
| 167-A01-force-bridge | 已合并 | 09-15 1946Z | #179 | — | A01 **行 (v) 数据/外力桥**（HANDOFF P7b）：forceOfPath F ↦ f' 与 MemForceR/MemL1Hm，a.field ∈ initialClassR，与 C01.forcePath 的往返 |
| 168-A01-pressure-p3 | 已合并 | 09-15 1926Z | #177 | — | A01 **c4/c9 压力 P3**（HANDOFF P7c）：pressureOfVelocity（Leray 余投影的势 + 规范）、pressure_gradient MemLp、pressure_smooth（时间侧以 B1 为具名假设）、momentum 经 navierStokesResidual_eq_iff_projected |
| 169-A01-b1-ladder-r2 | 已合并 | 09-15 2003Z | #180 | — | A01 **B1 阶梯 R2**（HANDOFF P8）：datum 路径对时间可导，导数 = 动量残差的 datum（Duhamel 方程微分；路线 α vendor Duhamel 导数 + L2Descent 下降，或 β 光滑代表元切片）；任务书 collaboration/briefs/169-*.md |
| 170-C01-e6-e7-enstrophy-identity | 已合并 | 09-15 1944Z | #178 | — | C01 **E6/E7**（HANDOFF P2 后续）：enstrophyIdentity（代入动量方程、压力配对消去）与 h2TimeIntegral（H¹ 吸收门 ⇒ ∫₀ˢ‖u‖²_{H²} < ∞）；不注册（C01 V4 另开） |
| 171-SPEC-r41d-draft-a | 已并入 174 | 09-15 2002Z | — | — | R41D **定理 4.1 密度分支盲稿 A**（HANDOFF P11，规则 2）：只看论文 + Contracts/V1 + R42 已注册合同；产出 research/R41D/DraftA.lean + COMPARISON_A.md |
| 172-SPEC-r41d-draft-b | 已并入 174 | 09-15 2002Z | — | — | R41D **盲稿 B**（与 171 互不可见，同样输入）：DraftB.lean + COMPARISON_B.md；两稿完成后 lead 比对 → COMPARISON.md → Spec.lean |
| 173-A01-hinv-invariance | 已合并 | 09-15 2013Z | #182 | — | A01 **行 (iv) 角不变性 hinv**（HANDOFF P9a）：路线 α 平移等变 + mild 唯一性 ⇒ HasAprioriBound 量化的每个 Duhamel 解自动角不变；路线 β 限制量化并重闭消费者环 |
| 174-SPEC-r41d-compare | 已合并 | 09-15 2004Z | #181 | — | R41D **盲稿 A/B 比对与调和**（规则 2 第三人）：COMPARISON.md（逐条 论文↔A↔B）、RECONCILIATION.md、定稿 Spec.lean（可 elaborate）；合并两稿的上游缺口 G 表 |
| 175-R43-s1-pairing | 已合并（#185，wave 12 门禁 154 模块绿、28 合同） | 09-15 2112Z | #185 | — | R43 **S1 恒等式层**（HANDOFF P5）：临界路径 y² 的 datum 形定义、⟪Δu,Λu⟫ = −z²、⟪∇p,Λu⟫ = 0、⟪f,Λu⟫ ≤ by，装配成 henergy 形，只留 htri（三线性估计）与 hcrit（半阶齐次 datum 路径）两条具名假设 |
| 176-MAINT-simp-codex-batch | 已合并（#188，wave 15 门禁绿） | 09-15 2143Z | #188 | — | MAINT **SIMP/tester 通道**（HANDOFF P10）：161/162/163/164/166/168/170 七个 codex 模块的简化与测试、156/157 遗留 note（Spec 行号、sqrt_energy_le_primitive' 上提到 Paper1、SliceWiring 别名/泛化）、合同闭包计划 CLOSURE_PLAN.md（A01 V2 / C01 V4 bundle）；被消费陈述逐字节不变 |
| 177-C01-v4-contract | 取消（owner 在 main 已注册完整 C01 V4：C01.energy_absorption_v4 六字段含 enstrophyIdentity/h2TimeIntegral；我们的 V4 被覆盖） | 09-15 2031Z | — | — | C01 **V4 合同**（第 28 条）：extends V3 + enstrophyIdentity（逐 token 抄 Spec.lean:487）；h2TimeIntegral 仍排除（170 只证了严格内部） |
| 178-A01-b1-ladder-r3 | 已合并（#186，wave 13 门禁绿） | 09-15 2134Z | #186 | — | A01 **B1 阶梯 R3**：datum 路径的 C^j 时间正则（残差路径可导、tame 积的 Leibniz、逐阶损失记账；全阶版以供给侧界为具名假设） |
| 179-A01-gronwall-endpoint | 已合并 | 09-15 2027Z | #184 | — | A01 **行 (iii-b) Grönwall 端点**：把 149 的端点帽喂进 Grönwall 得整个 Ico 0 T 上不退化的显式界 + A04 restartBeyond 输入形状的一致 H¹ 界 |
| 180-A01-b2-assembly | 已合并（#190，wave 30 门禁绿；ConstructorAssembly.lean 在集成分支：经典解构造器条件于 hb 与 PressureSupply） | 09-16 0045Z | #190 | — | A01 **B2 装配**：用已合入部件（161/162/167/168/169/173 + 153/157）装出有条件的 ClassicalSolutionR 构造子 carrierConstructor_of_localTheory，只留联合光滑性 hc3（B1 R3/R4）与可能的 hcurl 为具名假设；CarrierConstructorFull 形状 + 消费者环探针 |
| 184-MAINT-merge-main | 已合入集成分支（c0f4439；门禁 153 模块绿、28 合同、vs main 兼容；修了 ForceBridge 的 import） | 09-15 2110Z | #— | — | MAINT **合并 main（owner PR #161–#171）进集成分支**：同路径冲突取 main 版本、我们的改名保留（C01/EnstrophyIdentityRaw、A01/ConstructorDivergenceSlice）；contracts.json = main 的 C01 V4 + 我们的 D01.homogeneous_norm（28 条）；记录文件两边保留；main 新模块：A04/Continuation（restartBeyond/lifespan 条件版）、C01/H2TimeIntegral + EnstrophyBounds + SobolevTwo、R43/MaximalEndpoint（G5）、A01/ConstructorDatumPath + ForcedMaximalRegularity + ForcedSourceUpgrade + HeatGradientTrace |
| 181-A05-v2-contract | 已合并（#187，wave 14 门禁绿；第 29 个合同 A05.gradient_l6_v2） | 09-15 2137Z | #187 | — | A05 **V2 合同**：把 165 的 velocityCriticalL3 注册为 `A05.gradient_l6_v2`（第 29 个合同），Ḣ^{1/2} 范数走已注册的 D01.homogeneous_norm |
| 182-R43-s1b-trilinear | 已合并（#192，wave 19 门禁绿） | 09-15 2150Z | #192 | — | R43 **S1b 三线性估计** abs ⟪(u·∇)u,Λu⟫ ≤ C₀·y·z²：Hölder 三个 L³ 因子 + 165 的临界嵌入（含导数版），目标恰为 175 的 `CriticalTrilinearEstimate` |
| 186-A01-a3-common-horizon | 已合并（#189，wave 16 门禁绿；A3-U 条件于 MildUniqueness，188 在证） | 09-15 2143Z | #189 | — | A01 **A3-U 公共视界**：由 ∀q HasAprioriBound 得到一条 U 在每个柱阶实现（跨阶唯一性），恰好供给 178 的 `hall`（去掉力光滑性 hfs）；178/180 共同指出的 A01 真正卡点 |
| 187-A01-hfs-force-path | 已合并（#193，wave 20 门禁绿；hfs 卸下） | 09-15 2202Z | #193 | — | A01 **B1 供给 hfs**：`C01.forcePath hf` 的柱值路径 `sobolevPath F hF q` 在时间上 C^∞（MemForceR 的光滑 datum 路径经连续线性重构）；178 审稿确认树里缺这座桥，178/186 都以它为输入 |
| 188-A01-mild-uniqueness | 已合并（#191，wave 18 门禁绿；A3-U 现在只剩全阶先验界与 hfs 两个供给输入） | 09-15 2149Z | #191 | — | A01 **MildUniqueness**：6 阶 mild 解（quadraticDuhamel 不动点）在整个 [0,S] 上唯一——186 的唯一命名输入；路线：小窗口压缩（vendor mild_solution_unique 要 kernelMass·L<1）+ 重启/首次分离时刻迭代 |
| 189-A01-pressure-regularity | 已合并（#203，wave 31 门禁绿；压力腿闭合；A01 构造器管线探针：仅由 hb 得到经典解） | 09-16 0057Z | #203 | — | A01 **P4 压力梯度正则性**：G = residual − ∂ₜu 在开板 [0,S)×R³ 上 C∞、逐时 L²（Leray 余项）、对称 Jacobian（余项是梯度）——180 的 `hpg`；输入 hc3/hsob/散度/169 的投影动量恒等式 |
| 190-A01-b1-r4-joint-smooth | 已合并（#194，wave 21 门禁绿；JointRepresentative.lean 在集成分支） | 09-15 2253Z | #194 | — | A01 **B1 R4 联合光滑代表元**：由 178 的全阶 C^j_t 数据路径造一个 u(t,x)，切片 a.e. 等于 U t 且在 [0,S)×R³ 上联合 C∞（Sobolev 嵌入 + 连续线性求值）——180 的 `hc3`；新增可满足性规则 |
| 191-A05-u4-shifted-data | 已合并（#195，wave 22 门禁绿；R43 桥只剩 Parseval 配对） | 09-15 2303Z | #195 | — | A05 **U4/U8 → R43 桥的 shifted 字段**：H^∞ 场的物理 Λv 实现（Ḣ^{1/2} 数据 = v 的 Ḣ^{3/2} 数据）与 ∂_j v 的半阶数据 + Riesz 坐标符号；打包成经典解切片的 `ShiftedCriticalData`；Parseval 配对留给下一条 |
| 192-A01-wiring-hsob | 已合并（#196，wave 23 门禁绿；CylinderWiring.lean 在集成分支） | 09-15 2310Z | #196 | — | A01 **接线**：186′+188（公共视界无条件）+187（hfs）+178（全阶 C^j 数据路径）→ 仅由全阶先验界 hb 得到构造器的 hsob/hU/hdiv；记录 A01 管线剩下的唯一分析输入（A3-M2 的 hb，加 190 的 hc3、189 的 hpg） |
| 193-A01-a3-m2-bounds | 已合并（#197，wave 24 门禁绿；AprioriFamily.lean 在集成分支；A3 只剩 MildGronwall（196）） | 09-15 2315Z | #197 | — | A01 **A3-M2 全阶先验界族 hb**（最后一个 A3 分析单元）：基阶 6 的局部视界与半径先定 → 高阶解降阶+唯一性（186/188）等于基阶解 → H² 积分帽用基阶半径 → mild 级 Grönwall 给每个 R q；若 mild 级 Grönwall 缺则单独命名 |
| 194-A01-complement-path | 已合并（#199，wave 26 门禁绿；ComplementPath.lean 在集成分支） | 09-15 2348Z | #199 | — | A01 **P4a 余项路径**（189 重设计的一半）：残差 νΔu+f−(u·∇)u 的 Leray 余项在每个阶的 C^j_t 数据路径 + 一条物理路径 w + 逐时"w t 是残差 0 阶数据的余项"；经 190 得联合光滑场 G |
| 195-A01-interior-momentum | 已合并（#200，wave 27 门禁绿；InteriorMomentum.lean 在集成分支） | 09-15 2351Z | #200 | — | A01 **P4b 内点动量恒等式**（189 重设计的另一半）：190 联合代表元的 ∂ₜu = 导数数据的求值（有界求值与 fderiv 交换）+ 代表元线性 ⇒ 在 Ioo 0 S 上 G = residual − ∂ₜu；t=0 不作任何断言 |
| 196-A01-mild-gronwall | 已合并（#198，wave 25 门禁绿；A3 只剩 FiniteMildEnergy（198/199）） | 09-15 2346Z | #198 | — | A01 **MildGronwall**（A3 最后一个分析输入）：vendor 正则化 mild 能量链 `mild_majorized_energy_subinterval` 特化到常欧氏度量与 q+1 阶有限 word 族，顶阶非线性项走 A03.outerProductTame → A04.outerSobolevNormAt_le → A04.inner_energy_Rhigh；显式 E q, C q |
| 197-A01-leray-bridge | 已合并（#201，wave 28 门禁绿；LerayBridge.lean 在集成分支） | 09-16 0029Z | #201 | — | A01 **P4c 投影桥 hprojected**（195 的唯一命名输入）：柱面 Leray 投影 `leray 1 q` 与数据级 Fourier `lerayComplement 0` 在下降数据上一致——梯度部分纵向、投影部分无散、物理残差数据与下降柱面残差一致（`physicalResidual_datum_eq`，194 也用） |
| 198-A01-energy-premises | 已合并（#202，wave 29 门禁绿；MildEnergyPremises.lean 在集成分支） | 09-16 0044Z | #202 | — | A01 **A3-M2 能量前提**（FiniteMildEnergy 上半）：为柱面 NS 解构造 vendor `mild_majorized_energy_subinterval` 的前提（无散路径、梯度压力、最大正则 Bochner 态 U∈TimeLp(H^{q+2})、源/压力代表元及限制恒等式），恒等度量、全 word 族 N=q−5；导出积分根能量估计，Z 的界与包络转换留给 199 |
| 199-A01-envelope | 已合并（#204，wave 32 门禁绿；MildEnergyEnvelope.lean 在集成分支；A3-M2 只剩 200 forcing 界 + 201 根比较） | 09-16 0118Z | #204 | — | A01 **A3-M2 包络**（FiniteMildEnergy 下半）：带号正则化能量恒等式保留 −ν 梯度平方 → 张量配对桥 + A03/A04 tame 界 → 极限后 Young 吸收 → 标量比较 ODE y′=αy+b 给处处可微包络 x=y²；同时证 ForcingFamilyBound（换位子族范数界） |
| 200-A01-forcing-bound | 已合并（#206，wave 34 门禁绿；ForcingFamilyBound.lean 在集成分支） | 09-16 0140Z | #206 | — | A01 **ForcingFamilyBound**（A3-M2 forcing 子行）：正则化柱面系统的 word 强迫/换位子族范数 ≤ tame 配对（vendor 换位子引理 → A03 outerProductTame → A04 outerSobolevNormAt_le → inner_energy_Rhigh；压力 word 项走柱面 Leray 投影有界性），显式 E(q),A(q) |
| 202-A01-commutator-bound | 已合并（#208）；补审 ACCEPT（astra：10 公理、常数变异按预期失败；审稿产物已入集成分支记录） | 09-16 0348Z | #208 | — | A01 **CylinderCommutatorBound**（A3-M2 最后两块之一）：柱面 word 换位子的 Kato–Ponce/Moser 估计——vendor 换位子恒等式展开 + 柱面 tame/插值引理（由 vendor OrdinaryTameProduct/WordInterpolation 模型经光滑逼近到相容有限 Sobolev 元）；先证存在常数 C(q)，再定显式常数或 re-cut A′ q |
| 201-A01-root-comparison | 已合并（#205，wave 33 门禁绿；RootComparison.lean 在集成分支） | 09-16 0132Z | #205 | — | A01 **CylinderRootComparison**（A3-M2 envelope 子行）：带号恒等式 + ForcingFamilyBound（作为假设）⇒ 正则化根的微分不等式 → 沿 198 的最大逼近族取带号积分极限 → 标量 Grönwall 比较（含零根极限与端点）⇒ FiniteMildEnergy 条件于 ForcingFamilyBound |
| 203-A01-signed-limit | 已合并（#207）；补审 ACCEPT（astra：12 公理、系数变异按预期失败；审稿产物已入集成分支记录） | 09-16 0354Z | #207 | — | A01 **CylinderSignedRootLimit**（A3-M2 最后两块之一）：把 199 的带号（保留 −ν 梯度平方）正则化能量不等式沿 198 的最大逼近族取积分极限——vendor 极限引理无耗散槽，需新增带号通道（强 TimeLp 极限经导数 word 映射或弱收敛下半连续）、ε 正则化根分母、先取极限再吸收；与 200 协调正则化族一致界 |
| 204-A01-signed-passage | 已合并（#209，wave 37 门禁绿；SignedPassage.lean 在集成分支；包络侧无条件） | 09-16 0248Z | #209 | — | A01 **CylinderSignedEnergyPassage**：199 的 n 级带号恒等式除以 ε 正则化根后积分，沿 198 的最大逼近族取极限（值族/强迫/度量收敛 + 203 的导数 word 平方积分收敛 + 控制收敛），保留耗散 |
| 205-A01-coordinate-tame | lead rebase+复核；PR 已开，合并链运行中（wave 38）；补审在跑 | 09-16 0456Z | #210 | — | A01 **CylinderCoordinateTame**：逐坐标柱面 Kato–Ponce/Moser 估计——word Leibniz 展开 + 柱面/下降 tame 插值引理 + 光滑逼近到相容有限元；允许 re-cut 到角不变子空间；先证存在常数 |
| 206-A01-smooth-tame | lead rebase+复核；PR 已开，合并链排队（在 205 之后，wave 39）；补审在跑 | 09-16 0456Z | #211 | — | A01 **SmoothCylinderCoordinateTame**（A3-M2 最后一条分析输入）：先走角不变 re-cut + 下降到 R³ 用 A03 tame 积（若成立则整个 A01 只剩接线，并导出无条件构造器探针）；退路是柱面插值本体或孤立精确的 R³ tame 不等式 |
| 207-A01-tame-assembly | 对抗式审稿 ACCEPT-WITH-NOTES（56 公理；两个变异按预期失败；备注为文档，已应用）；PR 已开，合并链排队（在 206 之后，wave 40） | 09-16 0456Z | #212 | — | A01 **tame 装配**（路线 A）：反向混合积估计 + Leibniz word 识别 + 组合求和 ⇒ SmoothCylinderCoordinateTame（显式 C q）⇒ 换位子界 ⇒ ForcingFamilyBound ⇒ FiniteMildEnergy ⇒ hb 无条件 ⇒ A01 无条件构造器探针；若 206 审稿推荐不变类 re-cut（路线 B）则改走 B |
| 208-A01-datum-horizon | 等 207 合入后自动建树启动（codex astra low，带重试） | 09-16 0458Z | — | — | A01 **合同注册 1/3**：初值识别 velocity(0,·)=a（连续 + a.e.）、initialClassR 桥、总函数 localHorizon 与 LocalTheoryAPI 的 solution 字段 |
| 209-A01-manuscript-regularity | 等 207 合入后自动建树启动（codex astra low，带重试） | 09-16 0458Z | — | — | A01 **合同注册 2/3**：ManuscriptLocalRegularity 四字段（全阶 C∞ 数据路径经 hslice；eq:Rpressure 含 t=0 由 189/194 的 Leray 余项恒等式；projected 由 momentum；径向势规范） |
| 210-A01-horizon-uniform | 等 207 合入后自动建树启动（codex astra low，带重试） | 09-16 0458Z | — | — | A01 **合同注册 3/3**：horizon_lower_bound——树支持的 H⁷ 球一致下界（vendor 时间预算单调性）；H¹ 子句（Tao H¹ 局部理论）诚实评估，给 lead/owner 两个选项（实现 H¹/H³ 定量局部理论 或 V2 re-cut 到 H⁷） |
| 160-A04-restart-beyond | 恢复完成；本地检查通过，PR 待审查 | 09-15 0659Z | — | #161 | `ForceShift` 证明正时间平移的 L¹Hˢ 范数单调性；`Continuation` 完成最大解场搬运和完整 δ 端点步。R1 保留精确 A02 `Restart`；`extendsBeyond` / C1 另保留精确 G3 `HigherOrderBound`。两项分析输入未在本 lane 证明，不注册为无条件合同。 |
| 161-A01-datum-path | 本地验收通过；PR 待审查 | 09-15 0731Z | — | #162 | 全阶定量下降控制 datum 差，构造所有 m ≤ q+1 的连续 RealVectorSobolev 路径；模块与顶阶消费者编译通过，七项公理仅标准三条；26条现有合同、13项保护测试、变异测试及base兼容性检查通过。独立 worktree 从 PR #161 的 0b8e5e4 派生。 |
| 162-C01-enstrophy | 本地验收通过；PR 待审查 | 09-15 0800Z | — | #163 | 装配 E5 梯度能量时导数、E6 压力消失与 E7 分部积分，完成精确 enstrophyIdentity、微分界和积分界（CRH1=2）；两模块及三个原Spec消费者编译通过，八项公理仅标准三条；26条现有合同、13项保护测试、变异及base兼容性检查通过。独立 worktree 从 PR #161 的 0b8e5e4 派生。 |
| 163-A01-divergence | PR待审 | 09-15 0830Z | — | #164 | 从 PR #162 / a4e18a2 派生；真无散下降及实际代表逐点散度。模块、8公理输出、26合同、政策/兼容与变异检查通过；旧constructor强迫范围已审计，尚非完整构造。 Astra low 编写/交叉审查，Luna high 编译。 |
| 164-C01-h2 | PR待审 | 09-15 0835Z | — | #165 | 从 PR #163 / 032e5bb 派生；真实datum H2比较CH2=16、时间积分Cassembly=32，含S=T。两模块、6公理输出、26合同、政策/兼容及变异检查通过；尚待完整C01合同注册。 Astra low 编写/交叉审查，Luna high 编译。 |
| 165-C01-full | PR已开，待云端CI/审查 | 09-15 0910Z | — | #166 | 完整C01 V4继承V3并增加原Spec六字段；双盲稿与独立陈述/绑定审查通过，27合同、负向及变异/Python门禁通过。Astra low 编写，Luna high 编译；尚未合并。 |
| 166-A01-maxreg | PR已开，待云端CI/审查 | 09-15 0915Z | — | #167 | 从 PR #164 / 65b2afb 派生；实际forced mild方程在原T上得到高一阶TimeLp及真实外力消费者。模块、五项公理、26合同、变异与Python检查通过；Astra low编写，Luna high编译。连续全阶塔仍未构造。 |
| 167-R43-endpoint | PR已开，待云端CI/审查 | 09-15 0935Z | — | #168 | 从 PR #166 / b436f72 派生；实际最大解族的吸收H2积分界推至有限最大寿命端点；保留原吸收前件，不假设终点经典解。 Astra low编写，Luna high编译。 |
| 168-A01-persistence | PR已开，待云端CI/审查 | 09-15 0942Z | — | #169 | 实际高阶TimeLp源及其降阶同一性；真实热方程终端梯度能量/耗散界。两个模块、九项公理、26合同、变异及Python检查通过；连续高阶极限仍待构造。Astra low编写，Luna high编译。 |
| 169-A01-plan | 方案复核 ACCEPT；PR 待审，云端账单阻塞 | 09-15 1015Z | — | #170 | 依据独立 Astra xhigh 审核：分离 H¹ budget、同区间 persistence 与 API；修正旧 H1/T1/X1 依赖；保留 lane 168，下一 lane 170。无 Lean 或合同改动。 |
| 其余节点 | 未开始 | — | — | — | |

## 9. 发现与 DAG 修正记录（历史，只追加；待 owner 的部分见各条）

- 加边 A03 → R42：定理 4.2 的"寿命 ≤ T"一步用了引理 A.1 的 H² → L^∞。
- 加边 A03 → A02：唯一性证明的 Grönwall 系数 ‖∇u₂‖_∞ 只靠 H² → L^∞ 才有限（appendix-a:120-123）；A03 的祖先闭包 {D01, U04, A05, U03} 无环。
- R41D 按外力子类（F_R / F_c / F_rd）参数化，并加边 R41D → R45；推论 4.5 和命题 4.6 都需要定理 4.2 的紧支撑修正，而不只是定理 4.1 的结论。
- R42 的合同要显式导出 u_ε − v 无散和紧支撑压力规范，定理 4.7 的证明用到；R47 允许多一个只依赖时间的常数 κ(t)。
- 定理 4.2 / 命题 4.6 / 定理 4.7 必须共用同一个 ε 族（一个线程化的见证），ε₀ 取所有约束的最小值。
- 齐次实现：一个定义 Ḣ^s = {ĥ 可测, |ξ|^s ĥ ∈ L²}（−3/2 < s < 3/2）可覆盖 4.3 / 4.2 / 4.6 三处用法，其余作引理；‖·‖_{Ḣ^{3/2}} 只需定义为量。

- **D01 需补（R43 调和发现，阻塞 R43/R44 陈述的非空洞性）**：(G3) `MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` 及齐次孪生——`MemForceR` 只给整数阶 datum 路径，半阶范数是 1/2 阶路径上的下确界，可能对所有真实 f 都是 ⊤，使小性假设空洞；(G2) 路径级 `‖f‖_{L¹_tḢ^{1/2}} ≤ ‖f‖_{L¹_tH^{1/2}}`（A05 只有空间切片版）——**042 关掉了不齐次的 G3；齐次 G3 与 G2 仍开：需要一般 H^∞ 切片的齐次 datum（乘子 |ξ|^{1/2}(1+|ξ|²)^{-1/4} 经 `weightedAngularFourier_realization`），树里只有 Schwartz/紧支的构造**；(G1) 把 datum 形式 `dotHomogeneousENorm` 提升为注册定义。
- **A04 G1 拆分（056，`research/A04/G1_SPLIT.md`）**：SL0=D1（done）、SL6/SL8（done）；阻塞：SL1=D2（`deriv G t` = ∂ₜu 的 datum，需 A01 的 C^∞_{t,x} 正则性——`HasSmoothSobolevPath` 单独不够）、SL2 动量方程 datum 形式（A01）、SL3 Laplace 恒等式（datum 侧阶移 + `gradientSobolevNormAt` 的 formalization 定义）、SL4=P2、SL5 `∇·(u⊗u)` 的 H^m 分部积分。**结论：G1 的核心就是 A01 的 datum 层正则性输出；下一步先做 A01 单元 A1/A2 的 spec 拆分，而不是继续在 A04 里堆。**
- **L9(c) 收敛为一个义务 P2（055）**：`∂ₜu(t,·) ∈ SmoothSquareIntegrableJets` ⟺ Leray 投影 `(I−P)` 在物理实场（角约定）的 H^m 上有界；HeliCorgi 港口只有 cycles 约定、复数、分布层面、零阶的 `r3LerayComplementL2`/`r3HelmholtzPressure_gradient`，桥（实线性 + 约定 + 分布↔经典 + L²→H^m）是独立单元。另：`∇p` 的 jet 无 `MemForceR f` 时**为假**（055 给出反例），所以 C01 U4/U7 必须带力项假设。
- **B02 spec 缺陷（068 发现，reviewer 证明为假）**：`homogeneousDatumSub`（`research/B02/Spec.lean:470`）无可积性假设时**为假**（总化积分 + 零 datum 反例）——`IsSliceDistribution` 的物理配对积分被总化，`z − w` 的配对需要 `integral_sub`，即 `Integrable (ψ·z_i)`、`Integrable (ψ·w_i)`；诚实形式 `isHomogeneousSliceDatum_sub_of_integrable` 已证，对角论证只用 Schwartz 分量（D01 的 `integrable_schwartz_mul_component`）所以不阻塞。B02 合同注册时用 V2 形式或去掉该字段。
- **R42 寿命拆分修正（072 reviewer）**：`IsSobolevPath` 可加性（`D01.isSobolevPath_add`）与 `F_R + C_c^∞ ⊆ F_R`（`D01.memForceR_of_compact_difference`，第二参数正是 `InsertionFamilyAPI.forceDifference_compact`）都已注册——`u_ε` 的 `sobolev` 字段只缺修正路径的时间连续性（`D01.contDiff_angularPath` + 时间截断，M）；`MemForceR g_ε` 是 S；严格 `referenceLifespan` 由 `A02.regularThrough_iff` 在 `T+δ` 一步得到（合同形状应为「regular through `T+δ`」）。
- **R42 寿命拆分（072，`research/R42/LIFESPAN_SPLIT.md`）**：`u_ε = v + w_ε + U_ε`，只有差 `w_ε + U_ε` 紧支；`u_ε` 的 `sobolev` 字段 = `reference.sobolev`（非紧支路径）+ 紧支修正的 datum 路径，缺 **D01 的 `IsSobolevPath` 可加性 + 修正路径的时间连续性**（阻塞 ≤ 与 ≥ 两半）；`referenceLifespan` 子句是严格 `<`，`InsertionFamilyAPI.reference` 只给 `≤`（需要参考解 regular *through* `T+δ` 或 A02 的自带余量 `δ_A` 的同定）；`hg : MemForceR g` 必须加进 R42 V2。已证：limsup 转移、L^∞ 反三角、紧支场的全阶 datum。
- **SL6 = `∂ⱼ` datum 引理已证（066，`D01/DerivativeDatum.lean`）**；SL3 只剩配对恒等式 `⟪G, L⟫ = −Σⱼ‖D_j A‖²`：需要角约定方向导数乘子在 L² 上的**反自伴性**与 `angularOrderLowering` 的自伴性（符号纯虚/实），必须在角约定 L² 里直接证——`cyclesToAngular` 带 ξ 相关权重，不是等距的常数倍，恒等式不能从 cycles 约定搬运。
- **P2 拆分修正（062 reviewer）**：SL3 不是新基础设施——`vendor/HeliCorgi/Formal/R3LerayPointwiseL2.lean` 已有基于同一符号的算子值 L² 乘子（~60 行，范数 ≤ 1），且 Mathlib `holderL` 取 `E := R3C →L[ℝ] R3C` 直接给出 CLM；九分量三角不等式只能给 ≤ 3。L3 不需要（路线 B 按符号定义 P，「杀无散场」是逐点纤维事实）。**真正的门：SL6 循环**——没有任何子引理先给出一个 datum；补零阶 Plancherel 引理 `MemLp 2 ⟹ IsSobolevDatum 0`（从 `pressure_gradient` 出发），再靠符号与阶权重交换升到任意阶。唯一实质引理：`∂ⱼz` 的 datum = `iξⱼ` · `z` 的 datum。
- **角约定 Plancherel 已建（059，`B02/LowHigh.lean` 内部：`angular_plancherel`、`eLpNorm_fourierIntegral_eq`、`coeFn_l2Fourier_ae`）**：树里此前只有 Schwartz 级与抽象 Lp 商级；这是 B02 单元 6 与 I03 U7c 的共同核心，下一条 SIMP/MAINT 车道应提升到 `Paper3`（或 `Section4/D01`）共享模块，不要在单元 6 里重复。
- **D2 已证（056，`A04/TimeDerivative.lean`）**：`2 ≤ m` 是本质限制（H^s ↪ C_b）；C01 在 0/1 阶要用时需经 `angularOrderLowering` 从 m=2 下推（缺 `A03.lowerDatum` 的 CLM 打包 + 向量版 `IsSobolevDatum.lower`）。
- **P2 拆分（062，`research/D01/P2_SPLIT.md`）**：符号代数已证（`LeraySymbol.lean`）；关键缺口 **SL3**：`RealVectorSobolev m` 上的算子值（坐标混合）Fourier 乘子 CLM——树里所有乘子都是标量或逐坐标对角的，要把 `holderL` 模板提升到 3×3 符号 `ξᵢξⱼ/‖ξ‖²` + `ContinuousLinearMap.pi` + `realProjectionTo`（M，新基础设施）；**SL4β = D01 单元 L3**（逐点无散的 L² 场落入闭无散子空间，L）；SL4α `div ∂ₜu = ∂ₜ div u`（S/M，未证）。路线选 B（本地角约定乘子），HeliCorgi 的复/cycles/零阶版本只做交叉核对。
- **D2 可关（056 reviewer 证明）**：把 datum 路径的 Hilbert 空间时间导数经 `Paper3.angularBoundedRepresentative`（CLM 到 `BoundedContinuousFunction`）+ `evalCLM` 变成逐点时间导数，再用 `A03.representative_ae` 钉住代表元、虚部为 0 的常函数导数、`angularRealization_boundedRepresentative` 转回 `IsSobolevDatum`；不需要 A01，不需要差商/控制收敛。同一「钉代表元」技巧应能缩短 SL2–SL4。056 续改中把它提成模块。
- **A04 新义务 D2（053 reviewer 发现）**：`HasSmoothSobolevPath` 只给出光滑 datum 路径 `G`，没有人断言 `deriv G t` 是 `∂ₜu(t,·)` 的 datum；G1 要用动量方程替换导数前必须先有这条（属 A01 产出路径的一部分，或 A04 自证：datum 路径的时间导数 = 时间导数的 datum，经 `IsSobolevDatum` 的唯一性 L1 + 差商极限）。
- **C01 U3 发现（050，reviewer 修正）**：能量恒等式的消费者需要 `∇p(t)` 为全阶 `SmoothL2Field`，而 `ClassicalSolutionR` 只给 `∇p` 的零阶 `MemLp` + 空间光滑。**唯一根缺口**：压力梯度 jet；时间导数由 `momentum` 代数读出（∂ₜu = f − (u·∇)u + νΔu − ∇p）。诚实修法只有一条：**椭圆正则性单元 L9(c)**（`Data.lean:621`：eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` 是类的定理不是字段；Leray 投影在每个 H^m 有界 + u⊗u 的 H^∞ 代数）。不能给 `ClassicalSolutionR` 加压力 datum 子句（会让 Lean 类比论文强、把义务推给 prop:local 的构造者）。L9(c) 原记为"卡 U05"，U05 已完成（HeliCorgi 已移植），可以开。
- **D01 定义缺口（037 发现，待 D01 V2）**：`Data.lean` 的 `dotHHalfENorm`/`dotHThreeHalvesENorm` 是逐点 Fourier 积分，对非 L¹ 的 H^∞ 场退化为 0；R43/R44/A05/C01 的 smallness 假设必须共用 datum-下确界的齐次范数（A05 的 `dotHomogeneousENorm`），否则错误实现可空洞满足。
