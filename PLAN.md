# PLAN.md — 第 3 节（环面 T³）计划入口
> 状态日期：2026-09-17（lead 快照）。
> 第 4 节已完成：37 个注册合同；[完整归档](archive/section4/README.md)。
> 第 4 节交付：冻结分支 `erenup/integration`；PR #259 → `main` 待 owner。
> 第 3 节核心分支：`erenup/integration-section3`；新 lane 从它开、PR 以它为 base。
> 当前阶段：**S3-0**（T10 数据层准备）。
> 当前状态与下一步：[NEXT_SESSION.md](NEXT_SESSION.md)。
> 表示层、DAG、阶段与台账规则：[SECTION3_PLAN.md](collaboration/SECTION3_PLAN.md)。
> 工作包：[HANDOFF.md](collaboration/HANDOFF.md)；规矩：[CLAUDE.md](CLAUDE.md)。
> lane 编号全局唯一、递增；本次 267，下一号 **268**；外部预留 300–399。

## 1. 节点 DAG

T10–T24 的目标、依赖、大小与 T01–T04 桶映射以 [SECTION3_PLAN §3](collaboration/SECTION3_PLAN.md#3-节点-dagt10t24挂到既有桶-t01t04) 的表为准。
关键路径：T10 → T11 → T18 → T19 → T21；障碍主线经 T12/T20 汇入 T21。

## 2. 分阶段推进

详见 [SECTION3_PLAN §5](collaboration/SECTION3_PLAN.md#5-并行串行安排等第-4-节收尾后启动)：
S3-0 数据层双盲陈述、定稿与 `T01.torus_data` 注册；S3-1 五个叶子；
S3-2 T11/T20 主线与缩放、修正等叶子；S3-3 插入、密度、主定理与边界装配。
台账工具暂不支持完成状态或新增节点；实时调度以本页和 NEXT_SESSION 为准，见 [维护报告](archive/section4/REPORT_267.md)。

## 8. 进度表

lane 号跨章节全局唯一；下一号 **268**。263–266 行逐字保留自旧表，行内状态为各自记录时的快照。
历史全部 lane 见 [Section 4 原表](archive/section4/PLAN_SECTION4.md#8-进度表)。

| 节点 | 状态 | UTC | 合同 | PR | 备注 |
|---|---|---|---|---|---|
| 263-SPEC-t10-draft-a | 草案 A 完成（sol，63 分钟）：系数侧 PeriodicSobolev s = lp (Fin 3 → ℤ) 2 载体、IsPeriodicDatum、periodicSobolevENorm、均值/均值零分解、Leray、压力规范、X_T/F_T/ClassicalSolutionT/maximalLifespanT/breakdownSetT/energyENormT；可 elaborate；COMPARISON_A 含 needs-a-lemma 清单；等草案 B 后 reconciliation | 09-16 1843Z | — | — | **Section 3 启动（S3-0）**：T10 周期数据层的双盲陈述草案 A——系数侧 H^s(T³) 载体、IsPeriodicDatum 桥、均值/均值零、周期 Leray、∫p=0、X_T/F_T/B/E_T/ClassicalSolutionT/maximalLifespanT（照抄 D01 架构） |
| 264-SPEC-t10-draft-b | 草案 B 完成（sol，15 分钟）：实子空间载体 WithLp 2 (Fin 3 → lp ℂ 2)|_{A(−k)=conj A(k)}、IsPeriodicDatum、均值零子模、IsSolenoidal + periodicLeray + graph、PressureGaugeT、breakdownSetInT 参数化 Y、E_T 拆分；lead 已写 research/T10/RECONCILIATION.md（以 B 为基，补齐次数据/范数，ClassicalSolutionT 对齐 Data.lean，类定义按论文行定） | 09-16 2138Z | — | — | T10 双盲陈述草案 B：同上，独立模型 |
| 265-SPEC-t13-draft-a | 草案 A 完成（sol，10 分钟）：LocalizationAPI 四字段（固定基本立方体、IsSpatialPeriodization 关系）；草案 B（任意平移立方体、periodize 函数、含尾和引理字段）；lead 已写 research/T13/RECONCILIATION.md（取固定立方体 + periodize + B 的字段名，尾和引理不作字段；范数词汇用 T10 定稿） | 09-16 1913Z | — | — | T13 **lem:localization 双盲草案 A**（第 3 节真正的新分析；从一开始可并行的叶子）：Gagliardo 双积分 I_R/I_T、核 K_s 与格点尾和、常数 c_s、eq:localization 的一致常数——LocalizationAPI 陈述 + COMPARISON_A |
| 266-SPEC-t13-draft-b | 草案 B 完成（astra）：见 research/T13/DraftB.lean + COMPARISON_B；等草案 A | 09-16 1909Z | — | — | T13 双盲草案 B：同上，独立模型 |
| 267-MAINT-archive-section4 | 已合入 #260（lead 手动合并；make check OK）；第 4 节文档归档到 archive/section4/，PLAN/NEXT_SESSION/HANDOFF 重写为第 3 节 | 09-16 2104Z | #260 | — | Section 4 工作文档归档；实时入口转向 Section 3；台账工具限制见 REPORT_267；下一 lane = 268 |
| 268-MAINT-ledger-t10-t24 | 已合入 #261（lead 直接合并；make check：45 个工作项一致）；T10–T24 进 DAG/台账（T10/T13 needs-specification，其余 ready） | 09-16 2114Z | #261 | — | MAINT **台账**：把 T10–T24 加进 formalization/blueprint/tasks.json（DAG）、DEPENDENCY_GRAPH.md 与 collaboration/work_items.json（按 SECTION3_PLAN §3/§6 与 REPORT_267 §3 的字段）；render；make check |
| 269-SPEC-t12-draft-a | 草案 A 完成（sol）：见 research/T12/DraftA.lean + COMPARISON_A；等草案 B | 09-16 2135Z | — | — | T12 **均值零 Sobolev 微积分与临界嵌入**双盲草案 A（eq:Rproduct、‖v‖_∞≤C‖v‖_{H²}、‖v‖₃≤C‖v‖_{Ḣ^{1/2}}；对应第 4 节 A03/A05） |
| 270-SPEC-t12-draft-b | astra 被路由切断（无产出）；改用 sol 重启 | 09-17 2054Z | — | — | T12 双盲草案 B |
| 271-SPEC-t16-draft-a | 草案完成：见 research/T16/（等配对草案/ reconciliation） | 09-17 2054Z | — | — | T16 **lem:potential 局部无散截断**双盲草案 A（径向向量势、Urysohn 截断、w_ε、eq:bgzero；对应第 4 节 I02） |
| 272-SPEC-t16-draft-b | 草案 B 完成（astra）：见 research/T16/DraftB.lean + COMPARISON_B；等草案 A | 09-16 2121Z | — | — | T16 双盲草案 B |
| 273-SPEC-t14-draft-a | 草案完成：见 research/T14/（等配对草案/ reconciliation） | 09-17 2054Z | — | — | T14 **包导入 + 能量**（thm:packet 接口、lem:packetenergy；复用 I01.packet）双盲草案 A |
| 274-SPEC-t14-draft-b | 草案完成：见 research/T14/（等配对草案/ reconciliation） | 09-17 2054Z | — | — | T14 双盲草案 B |
| 275-SPEC-t22-draft-a | 草案完成：见 research/T22/（等配对草案/ reconciliation） | 09-17 2054Z | — | — | T22 **有界区域范数层**（eq:restriction-norm、eq:zero-extension；常数与 ε 无关）双盲草案 A |
| 276-SPEC-t22-draft-b | 草案完成：见 research/T22/（等配对草案/ reconciliation） | 09-17 2054Z | — | — | T22 双盲草案 B |
| 277-SPEC-t10-spec | 完成（sol，16 分钟）：Spec.lean 51 个定义可 elaborate；COMPARISON 含 17 项 needs-a-lemma；lead 复核后直接合入 #262 | 09-17 2055Z | #262 | — | SPEC **T10 定稿**：按 research/T10/RECONCILIATION.md 合并草案 A/B → research/T10/Spec.lean（可 elaborate）+ COMPARISON.md（含 needs-a-lemma 并集 = T10 的证明 lane 清单） |
| 278-SPEC-t13-spec | 已合入 #263（lead 直接合并：elaborate 0 输出，字段对照 reconciliation/论文） | 09-17 2109Z | #263 | — | SPEC **T13 定稿**：按 research/T13/RECONCILIATION.md 合并草案 A/B，复用 T10 定稿词汇 → research/T13/Spec.lean + COMPARISON.md |
| 279-SPEC-t16-spec | 已合入 #266（lead 直接合并：elaborate 0 输出，字段对照 reconciliation/论文） | 09-17 2109Z | #266 | — | SPEC **T16 定稿**：按 research/T16/RECONCILIATION.md（B 的数据记录 CutoffData + LocalPotentialAPI，A 的引用，T10 词汇）→ research/T16/Spec.lean + COMPARISON.md |
| 280-SPEC-t14-spec | 已合入 #264（lead 直接合并：elaborate 0 输出，字段对照 reconciliation/论文） | 09-17 2109Z | #264 | — | SPEC **T14 定稿**：按 research/T14/RECONCILIATION.md（B 的 PacketEnergyAPI/PacketImportAPI + A 的族选择器；继承 I01 PacketAPI）→ Spec.lean + COMPARISON.md |
| 281-SPEC-t22-spec | 已合入 #265（lead 直接合并：elaborate 0 输出，字段对照 reconciliation/论文） | 09-17 2109Z | #265 | — | SPEC **T22 定稿**：按 research/T22/RECONCILIATION.md（B 的 domainSobolevENorm 定义 + 三字段 API）→ Spec.lean + COMPARISON.md |
| 282-MAINT-s4-full-build-astra | 完成：206 模块 219.6 s 0 错误；三门禁过；37 合同公理精确；报告已并入 erenup/integration 并评论 PR #259；发现 Bindings.Packet/Scaling 同名声明 navierStokesResidual_eq（单独编译无碍，合并导入冲突，待 owner） | 09-17 2118Z | — | — | MAINT 第 4 节交付物**独立完整编译**（基于冻结分支 `erenup/integration`，PR #259）：206 模块真实重 elaborate + 三门禁 + 37 合同公理审计 → `logs/SECTION4_FULL_BUILD_20260917_ASTRA.md`，与 Opus 报告对照 |
| 283-T10-canonical-module | 完成（模块 350 行、50 个声明；probe 陈述修正后的 TorusDataAPI；lake 自动识别 Section3）→ PR 已开，codex 审稿中 | 09-17 2118Z | — | — | T10 规范定义模块 `Section3/T10/PeriodicData.lean`（research/T10/Spec.lean 含 lead 修正 1 的全部定义逐字落成 Lake 模块，复用 Paper1/TorusCube；probe 把 TorusDataAPI 陈述在模块上）→ 证明 lane 的共同基座 |
| 284-T10-physical-bridge | 排队（待 283 合入；简报已写） | 09-17 2124Z | — | — | T10 证明：`torusLift_injective`/`torusLift_surjective`/`mean_decomposition`（物理层桥，ℤ³ 平移引理） |
| 285-T10-datum-basics | 排队（待 283 合入；简报已写） | 09-17 2124Z | — | — | T10 证明：`datum_unique`/`datum_real`/`meanZero_datum`（系数侧；常数场的 Fourier 系数、可积性合取项） |
| 286-T10-parseval | 排队（待 283 合入；简报已写；astra 优先） | 09-17 2124Z | — | — | T10 证明：`parseval_forward`/`parseval_backward`（Mathlib `mFourierBasis` Hilbert 基，L² ↔ ℓ²） |
| 287-T10-leray | 排队（待 283 合入；简报已写） | 09-17 2124Z | — | — | T10 证明：`leray_exists_contraction`/`leray_projector`（纯 ℓ² 代数：压缩、实性、solenoidal、幂等） |
| 288-SPEC-t11-draft-a | worktree 安装中→自动启动（codex sol xhigh） | 09-17 2124Z | — | — | SPEC **T11 双盲草案 A**：`prop:local` on T³（存在/唯一/最大寿命/`eq:criterion` 延拓）+ Appendix A 均值消去与 ν 重标度；镜像 A01/A04 V2 合同形状 |
| 289-SPEC-t11-draft-b | worktree 安装中→自动启动（codex sol xhigh） | 09-17 2124Z | — | — | SPEC **T11 双盲草案 B**（同上，互不可见） |
| 290-SPEC-t12-spec | worktree 安装中→自动启动（codex sol xhigh） | 09-17 2126Z | — | — | SPEC **T12 定稿**：按 research/T12/RECONCILIATION.md（B 为基 + A 的常数名；修正后的 T10 词汇；Type 值 `MeanZeroSobolevCalculusAPI`，9 个字段含新增 `lambda_exists`/`homogeneous_le_sobolev`）→ Spec.lean + COMPARISON.md |
