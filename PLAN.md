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
| 283-T10-canonical-module | 已合入 #267（codex 审稿 ACCEPT：保真/公理/非空/负向变异全过） | 09-17 2250Z | #267 | — | T10 规范定义模块 `Section3/T10/PeriodicData.lean`（research/T10/Spec.lean 含 lead 修正 1 的全部定义逐字落成 Lake 模块，复用 Paper1/TorusCube；probe 把 TorusDataAPI 陈述在模块上）→ 证明 lane 的共同基座 |
| 284-T10-physical-bridge | 已合入 #271（codex 审稿 ACCEPT） | 09-17 2312Z | #271 | — | T10 证明：`torusLift_injective`/`torusLift_surjective`/`mean_decomposition`（物理层桥，ℤ³ 平移引理） |
| 285-T10-datum-basics | 已合入 #273（codex 审稿 ACCEPT）；TorusDataAPI 十字段全部进树 | 09-17 2328Z | #273 | — | T10 证明：`datum_unique`/`datum_real`/`meanZero_datum`（系数侧；常数场的 Fourier 系数、可积性合取项） |
| 286-T10-parseval | 已合入 #269（codex 审稿 ACCEPT，含 L²→L¹ 变异探针） | 09-17 2310Z | #269 | — | T10 证明：`parseval_forward`/`parseval_backward`（Mathlib `mFourierBasis` Hilbert 基，L² ↔ ℓ²） |
| 287-T10-leray | 已合入 #272（codex 审稿 ACCEPT） | 09-17 2320Z | #272 | — | T10 证明：`leray_exists_contraction`/`leray_projector`（纯 ℓ² 代数：压缩、实性、solenoidal、幂等） |
| 288-SPEC-t11-draft-a | 完成（草案 A；与 289 一起 reconciliation） | 09-17 2336Z | — | — | SPEC **T11 双盲草案 A**：`prop:local` on T³（存在/唯一/最大寿命/`eq:criterion` 延拓）+ Appendix A 均值消去与 ν 重标度；镜像 A01/A04 V2 合同形状 |
| 289-SPEC-t11-draft-b | 完成（草案 B；待 288 后 reconciliation） | 09-17 2215Z | — | — | SPEC **T11 双盲草案 B**（同上，互不可见） |
| 290-SPEC-t12-spec | 已合入 #268（lead 直接合并：elaborate 0 输出，9 字段对照 reconciliation，rfl 拼写检查） | 09-17 2300Z | #268 | — | SPEC **T12 定稿**：按 research/T12/RECONCILIATION.md（B 为基 + A 的常数名；修正后的 T10 词汇；Type 值 `MeanZeroSobolevCalculusAPI`，9 个字段含新增 `lambda_exists`/`homogeneous_le_sobolev`）→ Spec.lean + COMPARISON.md |
| 291-SPEC-t15-draft-a | 完成（草案 A；与 292 一起 reconciliation） | 09-17 2357Z | — | — | SPEC **T15 双盲草案 A**：`prop:scaling`（`eq:scaling` 放置/重标度/单拷贝周期化；`eq:packetEscale/Fscale/Hs`；镜像 `I03.scaling`，复用 T14 包与 T13 localization） |
| 292-SPEC-t15-draft-b | 完成（草案 B；待 291 后 reconciliation） | 09-17 2346Z | — | — | SPEC **T15 双盲草案 B**（同上，互不可见） |
| 293-T01-torus-data-contract | 已合入 #275（codex ACCEPT-WITH-NOTES，备注并入 296）：T01.torus_data 注册完成，合同数 38 | 09-18 0003Z | #275 | — | **注册第 3 节第一个合同 `T01.torus_data`**：`Contracts/V1/TorusData.lean`（数据层定义逐字重述 + 10 字段 `TorusDataAPI`）+ Bindings（rfl 桥 + 由四个证明模块装配）+ Tests；解类部分推迟到 T11 注册 |
| 294-SPEC-t17-draft-a | 路由切断（有 DraftA.lean）→ 02:11Z 续跑简报重启（sol） | 09-18 0211Z | — | — | SPEC **T17 双盲草案 A**：`lem:correction`（`eq:H` 修正力、`eq:derivativebounds/wE/Hmixed/HHs`；复用 T16 截断与 T13 localization；镜像 `I02.correction(_v2)`） |
| 295-SPEC-t17-draft-b | 完成（草案 B，续跑后；待 294 后 reconciliation） | 09-18 0128Z | — | — | SPEC **T17 双盲草案 B**（同上，互不可见） |
| 296-MAINT-t10-instance-dedupe | 已合入 #279（codex 审稿 ACCEPT）：单一命名实例，Bindings 直接装配十定理（161 行） | 09-18 0031Z | #279 | — | MAINT：T10 三个证明模块的匿名 `IsProbabilityMeasure` 实例同名冲突 → 在 `PeriodicData.lean` 命名一次、删重复；`Bindings/TorusData.lean` 改回直接装配十个定理（删 293 的私下重证） |
| 297-T12-canonical-module | 已合入 #274（lead 直接合并：定义类模块，probe 含 rfl 检查） | 09-17 2356Z | #274 | — | T12 规范定义模块 `Section3/T12/MeanZeroCalculus.lean`（research/T12/Spec.lean 的新定义逐字落成 Lake 模块，import T10 模块；probe 把 Type 值 `MeanZeroSobolevCalculusAPI` 陈述在模块上）→ T12 证明 lane 基座 |
| 298-SPEC-t11-spec | 已合入 #277（lead 直接合并：elaborate 0 输出，3+8+5+6+4 字段对照 reconciliation） | 09-18 0012Z | #277 | — | SPEC **T11 定稿**：按 research/T11/RECONCILIATION.md（`SolvesBelowT` 延拓假设、数据定义的 Galilean 均值、Poisson 压力、四个 API 结构 3+8+5+6+4 字段）→ Spec.lean + COMPARISON.md |
| 299-T13-canonical-module | 已合入 #276（lead 直接合并：定义类模块，probe 含 rfl 检查） | 09-18 0007Z | #276 | — | T13 规范定义模块 `Section3/T13/Localization.lean`（research/T13/Spec.lean 新定义逐字落 Lake 模块，import T10；probe 把 `LocalizationAPI` 陈述在模块上）→ T13 证明 lane 基座 |
| 300-T12-spectral-gap | 已合入 #280（codex 审稿 ACCEPT，含更小常数变异探针） | 09-18 0036Z | #280 | — | T12 证明：`spectralGap`（常数 `(1+1/(4π²))^(s/2)`）+ `homogeneous_le_sobolev`（常数 1）—— 系数侧权重比较与 lp 重加权构造 |
| 301-SPEC-t15-spec | 已合入 #278（lead 直接合并：elaborate 0 输出，21 字段对照 reconciliation） | 09-18 0025Z | #278 | — | SPEC **T15 定稿**：按 research/T15/RECONCILIATION.md（B 为基；`PlacementData` 参数；Type 值 `ScalingAPI` 含 `sobolevConst` 与 `forceConvergence`；import 已注册的 `T01.torus_data`）→ Spec.lean + COMPARISON.md |
| 302-T11-canonical-module | 已合入 #281（lead 直接合并：定义类模块 + 实现候选调查 → T11 拆分依据） | 09-18 0039Z | #281 | — | T11 规范定义模块 `Section3/T11/LocalTheory.lean`（新定义逐字落 Lake 模块；probe 把五个 API 陈述在模块上；附 Paper1/HeliCorgi 实现候选调查 → T11 证明 lane 拆分依据） |
| 303-SPEC-t20-draft-a | 路由 5/5 重连后切断（无产出）→ 01:39Z 原简报重启（sol） | 09-18 0139Z | — | — | SPEC **T20 双盲草案 A**：`prop:critical`（均值消去、`eq:criticalenergy/bintegral/ybound/H1energy`、经 `eq:criterion` 全局；镜像 R43+C01+A04） |
| 304-SPEC-t20-draft-b | 路由切断 → 01:44Z 重启（sol；原简报） | 09-18 0144Z | — | — | SPEC **T20 双盲草案 B**（同上，互不可见） |
| 305-T10-fourier-calculus | 已合入 #282 作为**部分交付**（审稿 REJECT 仅因范围遗漏 T10 第 11/12 项，已证内容审计/公理/变异全过）→ 312 补齐 | 09-18 0101Z | #282 | — | T10 基础引理：光滑周期场的 Fourier 微积分（导数符号 `2πi k_j`、Laplacian 符号、系数快速衰减、可和性与逐点反演、sup 界）→ 解锁 T12 `boundedRepresentative`/`lambda_exists`/`hTwo_le_laplacian` 与 T13 |
| 306-SPEC-t24-draft-a | 排队（简报已写） | 09-18 0040Z | — | — | SPEC **T24 双盲草案 A**：`prop:affine`/`prop:multiple`/`prop:conservative`（三个独立结构；基于 T14/T15 定稿） |
| 307-SPEC-t24-draft-b | 排队（简报已写） | 09-18 0040Z | — | — | SPEC **T24 双盲草案 B**（同上，互不可见） |
| 308-T11-U1-flow-conversion | 已合入 #284（codex 审稿 ACCEPT） | 09-18 0144Z | #284 | — | T11 U1：`ClassicalSolutionT ↔ Paper1.PeriodicLifespan.Flow` 逐字段转换 + 往返 + 两条拼写引理（S–M，sol） |
| 310-T11-U3-galilean-classes | 已合入 #287（codex 审稿 ACCEPT） | 09-18 0243Z | #287 | — | T11 U3：`translation_preserves_sobolev`/`transformed_classes`/`transformed_mean_zero`（M，sol） |
| 311-T11-U9a-existence-probe | 已合入 #283（codex 审稿 ACCEPT）：R2 路线、两空间契约、热半群第一阶 | 09-18 0139Z | #283 | — | T11 U9a：周期局部存在性路线探针（R1 HeliCorgi 端点层 vs R2 A01 柱面路线），具名输入 `PeriodicQuantitativeLocalInput`，至少证一条归约/一阶（L，astra） |
| 309-T11-U2-criterion-bridge | 已合入 #285（codex ACCEPT-WITH-NOTES：仅 markdown 笔误） | 09-18 0200Z | #285 | — | T11 U2：光滑周期场各阶 datum 存在与有限性、`squaredHTwoIntegralT ≠ ⊤ ↔ FiniteH2Energy (toFlow w)` 双向（L，astra） |
| 312-T10-force-paths | 排队（简报已写） | 09-18 0105Z | — | — | T10 第 11/12 项（305 审稿指出的遗漏）：`MemForceT` 力的各阶系数路径（连续/可测、`L¹_tH^m`/`L²_tH^m` 有限）+ 向量梯度/能量物理-系数恒等式 + 向量场分量推论 |
| 313-T11-U9b-existence-construction | 已合入 #286（codex 审稿 ACCEPT）：强迫 Picard 不动点；剩一个具名输入 TorusConvolutionInput → 317 | 09-18 0214Z | #286 | — | T11 U9b：按 311 定的 R2 路线，具名输入改为按阶力界的 `PeriodicQuantitativeLocalInput'`（lead 修正 1，`research/T11/LEAD_AMENDMENTS.md`）；证 EXISTENCE_ROUTE 的前两项（投影对流符号的双线性估计、强迫 Picard 不动点与寿命下界） |
| 314-T11-U4-rescaling | worktree 安装中→自动启动（codex sol xhigh，astra 备用） | 09-18 0243Z | — | — | T11 U4：粘性代数 `inverse_identities`/`scaled_classes`（S，sol） |
| 315-T11-U5-uniqueness | 排队（简报已写） | 09-18 0203Z | — | — | T11 U5：唯一性包 `velocity_unique`/`pressure_unique`/`horizon_le_lifespan`（复用 Paper1 `normalized_flows_agree`）（M，sol） |
| 316-T11-U7-mean-identity | 排队（简报已写；astra） | 09-18 0203Z | — | — | T11 U7：均值恒等式 `mean_formula`/`mean_derivative`（积分动量方程，Haar 积分下求导）（L，astra） |
| 317-T11-U9c-convolution-bound | 已合入 #288（codex ACCEPT-WITH-NOTES：两处注释措辞）：TorusConvolutionInput 偿还，两空间契约有居民 | 09-18 0245Z | #288 | — | T11 U9c：偿还 313 的唯一具名输入 `TorusConvolutionInput`（投影对流卷积的有界双线性 H³×H³→H² 实现：离散 Sobolev 乘积估计，Peetre 不等式 + Cauchy–Schwarz + 格点可和）→ 两空间契约有居民 |
| 318-T11-U9d-physical-recovery | worktree 安装中→自动启动（codex **astra** low，sol 备用） | 09-18 0245Z | — | — | T11 U9d：物理恢复 —— 由强迫 mild 系数解在公共 horizon 上构造 `ClassicalSolutionT`（全阶 bootstrap、Fourier 反演得物理速度、Leray 压力、动量方程）+ `PeriodicLocalRegularity`；允许一个具名输入 |
