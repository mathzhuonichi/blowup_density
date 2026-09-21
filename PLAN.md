# PLAN.md — Phase 5：在 owner 的新 `main` 上关闭 6 个 Partial（2026-09-20 起）

> 状态来源：`origin/main` @ `1a1b53b6`（owner 2026-09-21 "Publish streamlined manuscript and verified Lean companion"，已合入我们的 #259/#270）。
> 我们的核心分支 **`erenup/core`** = `main` + 流程层（本文件、`CLAUDE.md`、`scripts/`、`.claude/`、`research/`、`logs/`、`archive/`、`collaboration/briefs`、`docs/`）。lane 从 `erenup/core` 开 worktree、PR 以它为 base、lead 合入。
> 交付：每关闭一组 Partial，从 `main` 切 `erenup/delivery-<n>`，只带 `formalization/ verification/ paper/ experiments/` 的差异，开唯一 PR 给 `main`（owner 上次合入后自己剥掉了流程层；这样交付他不用再剥）。
> 老计划归档：`archive/section3/`（PLAN_SECTION3、SECTION3_PLAN、HANDOFF、NEXT_SESSION_SECTION3）、`archive/section4/`。

## 0. owner 的现状（读 `README.md`、`formalization/blueprint/{DEPENDENCY_GRAPH,RESULT_MAP,CLOSURE_AUDIT}.md`、`output/pdf/formalization_guide.pdf`）

- 注册表精简为 **29 个合同**（去掉被取代的版本；T23 的边界插入改名 `T23.boundary_insertion_v2`，owner 自己证了 `ibp_boundedDomain`，G1 已闭）。
- 文章级清单 **21 Closed / 6 Partial**；两条主定理（Thm 3.1、Thm 4.1）Closed，规则："Closed 不得依赖 Partial"（`make check` 强制）。
- `research/`、`collaboration/`、`archive/`、`.claude/`、`scripts/` 全被删；`vendor/` 只留用到的模块；`FormalPatched` 删除，`formalization/lakefile.toml` 的 HeliCorgi roots 缩减、本地库改 `globs = ["NSFormalization.+"]`。
- 新检查：`make check`（`check_formalization_plan.py --check`、`check_contracts.py --summary`、`test_contract_policy.py`）、`make test`、`make test-mutations`、`audit_article_axioms.py --build --output-dir …`、`make paper`（`check_reader_documents.py`，需要 LaTeX，本机有 latexmk）。
- 蓝图数据：`proof_graph.json`（节点/状态/evidence/completion_from）、`entrypoints.json`（proof_modules）、`RESULT_MAP.md`、`AXIOM_AUDIT.json`、`DEPENDENCY_GRAPH.md`（由 `check_formalization_plan.py` 生成）；guide 表在 `paper/formalization_guide.tex`（`\coverage{Partial}` 行）。

## 1. 六个 Partial：评估、路线、lane

评估原则（用户 2026-09-20 反馈，见 `logs/LESSONS.md` 顶部）：上次 478 把 `IBP Ω` 留成残差，owner 用零延拓 + "紧支撑 C¹ 函数的坐标导数积分为零"直接证掉；**剩下的 Partial 预期都是同类的管道活，不是新分析**（Prop 2.1 除外）。

| # | 条目（`proof_graph.json` 节点） | 缺什么（owner 原话） | 路线 | 规模 / 模型 | lane |
|---|---|---|---|---|---|
| P1 | Thm 3.6 prescribed ball（`G36_FULL`，`completion_from: G36`） | 原始数据构造用固定球（T15 `placementData` 圆心 (½,½,½)、半径 3/8）；对任意给定坐标球的量化未闭 | T15 加 `placementDataAt center radius`（T24 `RegionsData.placement` 已是这个形状）；T19 `insertionDataAt`/`insertionAt` + 导出引理；原始数据定理 `periodicInsertion_from_data`（∀ 球，`closure ball ⊆ interior cube`）；V2 合同 `T03.periodic_insertion_v2`（模型：owner 的 `Bindings/BoundaryInsertionV2.lean: boundaryInsertion_from_data`，球半径 `2r`） | M（管道） | 492 astra |
| P2 | Lemma 3.5 full scope（`C35_FULL`，from `C35_T`） | 注册的 `correctionStatementAmended` 带显式全局光滑/chart/0<ν 前提，由下游供给 | 文章形式：∀ 经典周期解 `reference : ClassicalSolutionT ν a g (T+δ)`、∀ 给定球、∀ ν>0（文章假设），∃ cutoff，`w_ε/H_ε` 的全部结论（eq:derivativebounds、wE、Hmixed、Hs）——经 `extendByZero` + `correctionStatementSlab'`，并给出窗口上与 `reference.velocity` 一致的引理；V2 合同 `T02.correction_v2` | M（管道，复用 T19 U0） | 493 astra（可与 492 并行，放置穿线） |
| P3 | Remark 3.13（`R313`，from `S33`,`C35_T`） | 没有单独导出的"力振幅发散"结论 | `⨆ ‖g_ε−g‖ ≥ ε⁻³‖F‖_∞ − Cε⁻²`：单拷贝周期化的 sup 范数缩放恒等式（T15）、`H_ε` 的逐点界 ε⁻²·C（T17 `rescaledForceProfile` 0 阶导数界 + `correctionForce = ε⁻²·profile`）、`‖F‖_∞ > 0`（F ≠ 0：否则 eq:packetenergy 给能量 0，与爆破矛盾；T14 `PacketEnergy`）；结论 `Tendsto (⨆ ‖g_ε − g‖) (𝓝[>]0) atTop` 挂在 T18/T19 的族上；新合同 `T03.force_amplitude`（1–2 字段） | S–M | 494 astra |
| P4 | Prop 3.17 bounded domain（`C317_B`，from `C317`,`BU`） | 有界域保守力变体未导出 | `ConservativeForcingOmegaAPI`（镜像环面 2 字段）：`∫_Ω (−∇φ)·u = 0`（owner 的 `IBP.integral_pressure_energy_zero` 就是它）+ 从静止出发 `u ≡ 0`（`NoSlipEnergy`/`DifferenceEnergy` 的能量恒等式 + 零能量⇒零）；`T04.conservative_forcing_v2` | S–M | 495 astra |
| P5 | Prop 3.16 bounded domain（`M316_B`，from `M316`,`B314`） | 有界域 no-slip 变体未装配 | 文章证明无背景：各分量 = 缩放包 `U_j`（I03），支撑在 `x_j + ε_j K_* ⊂ B_j ⊂ Ω`，和为 `ClassicalSolutionOmega`（光滑、div、动量、no-slip 因支撑在内部、压力 gauge、初值 0），每球 `SpeedUnboundedAtOn`，能量/耗散和；记录 `MultipleRegionsOmegaAPI` 镜像环面 30 字段（`ClassicalSolutionOmega` 替 `ClassicalSolutionT`，`Ω` 替方体）；`T04.multiple_regions_v2` | M–L（管道多） | 496 spec（astra，单稿 + lead 与环面记录/论文句逐字段比对）→ 497 证明（astra）→ 498 注册（sol） |
| P6 | Prop 2.1 general H¹ restart（`L21_H1`，from `L21T`,`L21R`） | Tao 的 H¹-uniform 局部存在/重启未形式化；已证 H³(T³)/H⁷(R³) 路线 | **真正的分析**：H¹ mild 解压缩映射 + 高阶正则传播。先做可行性评估（HeliCorgi `EndpointSafeTwoSpace*` 的空间、T11 `ExistenceInputH3`、A01/A04 现有工具；缺口清单、估计），再决定 | L–XL | 499 astra（只评估，出 `research/P21/ASSESSMENT.md`） |

每个 P 的收尾（同一 lane 或 500 系列 sol lane）：`proof_graph.json` 节点状态 → Closed、evidence 指向新模块、`entrypoints.json` 加 proof_modules；`RESULT_MAP.md` 行；`paper/formalization_guide.tex` 的 `\coverage{Partial}` 行改 Closed 并更新 `\source`；`python3 experiments/check_formalization_plan.py`（重生成 `DEPENDENCY_GRAPH.md`）；`audit_article_axioms.py --build`（更新 `AXIOM_AUDIT.json`）；`README.md` 的 "21 Closed / 6 Partial" 计数；合同注册 `contracts.json`（V2 条目格式见 `T23.boundary_insertion_v2`）；`make check/test/test-mutations`；`make paper`。

## 2. 顺序与并发（codex tmux，astra 硬活/sol 簿记审稿，<7 窗口）

1. **491** MAINT：`erenup/core` 上全量重编（owner 改了 lakefile/vendor）+ 四闸门 + 公理审计 —— 先确认环境。
2. 492、493、494、495、499 并行（互不依赖；492/493 都需要"任意球"的放置，各自本地定义或 493 穿线）。
3. 496 → 497 → 498（P5 链）。
4. 每个 P 审稿（sol）→ 合入 core → 蓝图/guide 更新 lane（sol）→ 阶段末 500 全量编译 + `make paper` → `erenup/delivery-1` PR 给 `main`。
5. P6 按 499 的评估另立阶段。

## 3. 进度表（UTC；lane 号全局递增，下一号见末行）

| lane | 状态 | 时间 | PR | 说明 |
|---|---|---|---|---|
| 491-MAINT-main-build-check | 已合入 #455（587 模块 rc 0，29 合同，四闸门 + make paper + 公理审计全绿；不绿：54 条本地 warning、Bindings/BoundedDomainNorm 三个 defProp） | 09-21 0353Z | #455 | owner 新 main（lakefile/vendor 变更）全量重编 + 四闸门 + `audit_article_axioms` |
| 492-T19-P1-prescribed-ball | worktree 安装中（两串各 3 个）→ codex astra | 09-21 0335Z | — | P1 Thm 3.6 任意给定球：placementDataAt + insertionAt + periodicInsertion_from_data + T03.periodic_insertion_v2 + 蓝图 |
| 493-T17-P2-article-scope | astra 完成 → 审中 sol | 09-21 0355Z | — | P2 Lemma 3.5 文章形式：correctionStatementArticle（经典参照 + 零延拓识别）+ T02.correction_v2 + 蓝图 |
| 494-T18-P3-force-amplitude | worktree 安装中（两串各 3 个）→ codex astra | 09-21 0335Z | — | P3 Remark 3.13：F ≠ 0、周期化缩放力的 sup 范数 ε⁻³‖F‖∞、H_ε ≤ Cε⁻²、发散 + T03.force_amplitude + 蓝图 |
| 495-T24-P4-conservative-domain | astra 8 分钟完成：ConservativeOmega.lean（pairing 经 IBP、restSolutionOmega、零能量⇒零）+ T04.conservative_forcing_v2（30 合同）+ 蓝图/guide/计数 22/5 + 四闸门 + make paper → 审中 sol | 09-21 0348Z | — | P4 Prop 3.17 有界域：ConservativeForcingOmegaAPI（pairing 经 IBP.integral_pressure_energy_zero；从静止为零）+ T04.conservative_forcing_v2 + 蓝图 |
| 496-T24-P5-spec-multiple-domain | 已合入 #456（astra 规范：30 字段，去 scaling 加 no_slip；lead 比对通过；entrypoints 补一行） | 09-21 0355Z | #456 | P5 步骤 1：MultipleRegionsOmegaAPI 规范（镜像环面 30 字段）+ canonical 记录 + 拆分 |
| 497-T24-P5a-domain-components-sum | worktree 安装中（core，含 496）→ codex astra | 09-21 0355Z | — | P5.1+P5.2：Ω 上的分量（无周期化缩放包 → ClassicalSolutionOmega）与有限和解（交叉输运为零、no-slip、gauge） |
| 500-T24-P5b-domain-blowup-energy | worktree 安装中 → codex astra，与 497 并行（穿线假设） | 09-21 0355Z | — | P5.3+P5.4：每球 region_agreement/region_blowup + 能量/耗散可加性（限制积分 = 全空间积分） |
| 499-P21-P6-h1-assessment | worktree 安装中（两串各 3 个）→ codex astra | 09-21 0335Z | — | P6 评估：Prop 2.1 H¹-uniform restart 缺什么、树里有什么、拆分与规模、建议（只出评估） |

下一号 **501**（501 = P5 装配 + T04.multiple_regions_v2 注册）。
