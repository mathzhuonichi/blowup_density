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
| 264-SPEC-t10-draft-b | 首轮（astra）81 分钟后被路由 Reconnecting 5/5 切断且未写出任何文件；已立即重启（astra 优先，失败换 sol） | 09-16 1901Z | — | — | T10 双盲陈述草案 B：同上，独立模型 |
| 265-SPEC-t13-draft-a | 草案 A 完成（sol，10 分钟）：LocalizationAPI 四字段（固定基本立方体、IsSpatialPeriodization 关系）；草案 B（任意平移立方体、periodize 函数、含尾和引理字段）；lead 已写 research/T13/RECONCILIATION.md（取固定立方体 + periodize + B 的字段名，尾和引理不作字段；范数词汇用 T10 定稿） | 09-16 1913Z | — | — | T13 **lem:localization 双盲草案 A**（第 3 节真正的新分析；从一开始可并行的叶子）：Gagliardo 双积分 I_R/I_T、核 K_s 与格点尾和、常数 c_s、eq:localization 的一致常数——LocalizationAPI 陈述 + COMPARISON_A |
| 266-SPEC-t13-draft-b | 草案 B 完成（astra）：见 research/T13/DraftB.lean + COMPARISON_B；等草案 A | 09-16 1909Z | — | — | T13 双盲草案 B：同上，独立模型 |
| 267-MAINT-archive-section4 | 已合入 #260（lead 手动合并；make check OK）；第 4 节文档归档到 archive/section4/，PLAN/NEXT_SESSION/HANDOFF 重写为第 3 节 | 09-16 2104Z | #260 | — | Section 4 工作文档归档；实时入口转向 Section 3；台账工具限制见 REPORT_267；下一 lane = 268 |
| 268-MAINT-ledger-t10-t24 | 已启动（codex sol xhigh，带重试；无需 lean-install） | 09-16 2104Z | — | — | MAINT **台账**：把 T10–T24 加进 formalization/blueprint/tasks.json（DAG）、DEPENDENCY_GRAPH.md 与 collaboration/work_items.json（按 SECTION3_PLAN §3/§6 与 REPORT_267 §3 的字段）；render；make check |
