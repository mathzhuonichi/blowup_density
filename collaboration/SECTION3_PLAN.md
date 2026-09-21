# SECTION3_PLAN.md — 第 3 节（环面 T³）形式化规划（快照：2026-09-16 02:50Z，lead）

> 本文件保留表示层与 DAG 的规划快照；第 4 节已完成，当前 **S3-0**，核心分支 **`erenup/integration-section3`**。
> 实时入口：[PLAN](../PLAN.md)、[NEXT_SESSION](../NEXT_SESSION.md)、[HANDOFF](HANDOFF.md)；第 4 节历史见 [归档](../archive/section4/README.md)。
> 节点 T10–T24 挂在既有 T01–T04 桶下；台账工具当前无新增/完成命令，限制及 lead 待办见 [REPORT_267](../archive/section4/REPORT_267.md)。
> 依据：论文侧与 Lean 侧两份只读调研及 HeliCorgi 核对。以下为设计快照，活状态以上述入口为准。

## 0. 三条结论（先看这个）

1. **T³ 几乎没人形式化过，仓库里也没有现成的 T³ 分析层。** 用户给的 [ns-mns2-flowmap-bridge](https://github.com/HeliCorgi/ns-mns2-flowmap-bridge) 就是我们已 vendor 的 HeliCorgi（`vendor/HeliCorgi` 固定在 `de51848`，128 个 Lean 文件），**纯 R³**（Leray/Stokes/投影 Duhamel/Picard/显式寿命/重启/爆破二分），无周期设定；"MNS2/flowmap" 是它的数值侧。OpenAI 包 `vendor/NavierStokesAndEuler` 也是 R³：`ProblemStatement.lean:11` 明说"单位环面由 R³ 上的周期函数表示"，`Euler/` 的"柱面"是 R³×S¹（一个辅助角方向），`UnitAddTorus` 只出现在一个 2 维 Fourier 对账处。Mathlib 提供 T³ 的**载体 + Haar 测度 + 多维 Fourier 正交基 + Parseval**（`Analysis/Fourier/AddCircleMulti.lean`：`UnitAddTorus`、`mFourierCoeff`、`mFourierBasis`、`hasSum_sq_mFourierCoeff`），其上的 Sobolev/齐次/均值零/热半群/Leray/Poincaré/嵌入**全部没有**。
2. **本地已有大量周期性工作，但用的是弱表示。** `formalization/NSFormalization/Paper1/Periodic*.lean` 146 个模块（无 sorry/axiom）：Fourier/Sobolev 脚手架（系数级 `lp (Fin 3 → ℤ) 2`）、热乘子、16 个 `PeriodicLeray*`、压力归一化、20 个 Picard/Duhamel、力规范/密度（`GaugeDense`、`forceDistance`）、寿命/局部理论接口、插入/局部化、12 个 critical、主装配 `PeriodicMain.lean`。**全部建在 `Space = R³` + 周期性 `Prop` 假设**（P 表示），真正的 `UnitAddTorus (Fin 3)` 只有 `Paper1/TorusCube.lean`（100 行：`torusLift`、`integral_torusLift`、`periodicFourierCoeff`、Parseval）。两处诚实的接口结构体是 `ClassicalPeriodicLocalTheory`（`PeriodicLocalLifespan.lean:73`）和 `CriticalRegularityCertificate`（`PeriodicCriticalRegularity.lean:63`）；`PeriodicMain.lean` 的 `paper1_main_with_critical_interfaces` 就是条件于这两者的 `thm:main`。**不要用** `NSFormalization/Citations/`（6 个占位 `axiom`，不在 umbrella）；`Paper1/BoundaryCorollary.lean:90` 是全库唯一的真 `sorry`（在 umbrella 里，T04 前要处理）。
3. **数学上第 3 节更简单，形式化上"准备工作多、核心证明短"。** 简单在：均值零场上 `H^s ≍ Ḣ^s`（谱隙），无低频问题（第 4 节的 eq:RL2、`q=2` 临界估计、B01/B02 完备化全部不需要），压力一个 `∫p=0` 归一化，力类按定义时间紧支，负阶自由。难在：**均值演化**（`m' = ḡ`、Galilean 平移 `v = u(·+X(t)) − m(t)`，仓库零覆盖）、`lem:localization`（周期化与 R³ 齐次范数的比较，第 4 节没有对应物），以及**一致的均值零 `H^{1/2} ↪ L³` 嵌入**（`PeriodicFiniteCriticalInterface.lean:4-7` 明说是开的，T01 合同禁止用有限模常数冒充）。

## 1. 表示层决策（最重要的设计选择）

两条路：(a) 把 146 个模块整体搬到 `UnitAddTorus (Fin 3)`；(b) **保留 (P) 作为物理场层，把全部分析放到系数侧** `lp (Fin 3 → ℤ) 2`，用 `TorusCube.lean` 的桥（`torusLift` / `integral_torusLift` / Parseval）做两个方向的兼容。

**决定：走 (b)，并照抄第 4 节 D01 的"数据形式"架构。** 理由：论文与 vendor 的问题陈述都是 (P)；146 个模块不必重写；第 4 节最成功的模式正是"物理场 `z` ↔ Hilbert 侧代理 `A`，中间用 `IsSobolevDatum` 桥"（`Contracts/V1/Data.lean:160`），在 T³ 上这个代理就是加权 `ℓ²(Z³)`，权 `(1+4π²|k|²)^{s/2}`，**没有 Schwartz、没有缓增分布、没有 `Real.fourierIntegral`**——第 4 节 D01 里最痛的"升阶无界"（`FiniteOrderDatum.lean:4-40`）在离散谱上消失，Leray 投影去掉 `k=0` 后是平凡有界的对角算子（`PeriodicLeray*` 已在系数级）。代价：第 4 节里凡是经 `angularRealization`/连续频率证的引理**不能搬**，要在系数侧重证（但都更短）。

## 2. 复用映射（什么能直接用、什么同型复制、什么必须新建）

| 类别 | 直接复用（零改动或实例化） | 同型复制（改载体、证明骨架照抄） | 必须新建 |
|---|---|---|---|
| 流程/架构 | `Contracts/Bindings/Tests` + `contracts.json` + `check_contracts.py`；codex lane 工作流（`scripts/codex_lane.sh`/`codex_review.sh`、简报四段报告、可满足性规则） | — | `T10.*`/`T11.*` 等合同 id（`parent_task: T01…T04`） |
| 局部理论骨架 | HeliCorgi 抽象层（**约 1/4 是定义域通用的**）：`MildEvolutionKernel`、`LerayProjectedQuadraticContract`、`EndpointSafeTwoSpaceDuhamelContract`/`Concatenation`/`Uniqueness`/`Restart`、`FlowMapContinuationPackage`、`FlowMapUniformRestartPackage`、`GronwallIntegralInequality`——全部在抽象 Hilbert `V` 上，**在 `V := 均值零无散 L²(T³)` 实例化即可** | 第 4 节 A01 的 `Horizon`/`HasAprioriBound`/`compatible carriers`/`MildUniqueness`（因果窗口）/`AprioriFamily`（基阶半径路线）的**论证结构**逐字同型，只是载体换成系数级 | T³ 热半群、T³ Leray、均值零子空间作为空间、Galilean 均值消去 |
| 能量恒等式 | `C01/EnergyIdentity.lean:82,103` `inner_energy_identity(_deriv)`、`A04/HighEnergy.lean:100` `inner_energy_assembly`（抽象内积空间，三条结构事实 `hlap/hpr/hnl` 作为假设） | — | 三条供给在 T³ 上用 Parseval 直接证（比 R³ 短） |
| 嵌入/tame | 第 4 节 A03/A05 的**陈述形状**与 R43 的 S1 配对/三线性装配 | `A05.velocityCriticalL3` 的 Riesz 路线换成谱隙 + 系数级 Hausdorff–Young；`A03.tame_products` 的 T³ 半（合同里明写 "not the torus half"） | 一致均值零 `H^{1/2}↪L³`（谱隙 + 系数级估计）、`‖∇v‖₆ ≤ C‖Δv‖₂`、`‖v‖_{H²} ≤ C‖Δv‖₂` |
| 插入脊柱 | `I01.packet`（合同 V1 已注册，且本来就引 `03-torus.tex`）、`I03.scaling` 的欧氏恒等式（`eq:packetEscale/Fscale`，`criticalOrder`/`scalingExponent` 纯算术）、`I01/Extension.lean` `extension_smoothOn`、`I03/Energy.lean` 切片引理（都是抽象 `V`） | `I02.correction` 的 R³ 内容（`lem:potential` 向量势、`w_ε` 的导数/能量/混合 Lebesgue 界——论文说"局部的，任何欧氏球都适用"） | `lem:localization`（`eq:localization`，常数对支撑收缩一致）——**唯一最高杠杆的新节点**：它把三个已注册的第 4 节合同一次性转成环面陈述；资产：vendor `NavierStokes/PeriodicLocalization.lean:58-62`（`translate`/`periodize`）、`Paper1/PeriodicBridge.lean:26-51`、`TorusCube.lean:40` |
| 密度/顶层 | `Paper1/PeriodicDense.lean`（`singularSlice`/`GaugeApprox`/`GaugeDense`）、`PeriodicMain.lean`（`GaugeSeparated`）、`PeriodicDensityFiber.lean`（`forceDistance`）、`PeriodicLifespan.lean`（`Flow`/`lifespan`）——纯序/拓扑，**已在周期侧写好** | 第 4 节 R41 装配的两分法 | 把 `CriticalRegularityCertificate` 与 `ClassicalPeriodicLocalTheory` 真正构造出来（这就是 T11 与 T20） |

## 3. 节点 DAG（`T10–T24`；挂到既有桶 `T01–T04`）

论文依赖图有两条**互不相交**的脊柱，只在 `thm:main` 汇合（论文 03:380-381 自己说明"障碍脊柱与紧支爆破定理无关"）：

- **构造脊柱**：`thm:packet → lem:packetenergy → prop:scaling → thm:insertion → prop:density → thm:main(i)`，`lem:localization` 与 `lem:potential/lem:correction` 汇入。
- **障碍脊柱**：`prop:local + lem:calculus + lem:critical-embeddings → prop:critical → cor:nondensity → thm:main(ii)`。

| ID | 目标（一句话） | 依赖 | 大小 | 镜像的第 4 节家族 | 桶 / 可复用 Lean |
|---|---|---|---|---|---|
| **T10** | 周期数据层：系数侧 `H^s(T³)` 范数、`X_T`/`F_T`/`B_{ν,a,T}`/`E_T`、均值/均值零分解、周期 Leray（`k=0` 处恒等）、`∫p=0` 规范；`TorusCube` 双向桥 | — | M | D01 | T01；`PeriodicSobolev*`、`PeriodicForceSpace`、`PeriodicMeanZero`、`PeriodicLeray*`、`PeriodicPressureNormalization`、`TorusCube` |
| **T11** | 周期局部理论合同（`prop:local` on T³）：存在/唯一/最大寿命 + 延拓判据 `∫₀^S‖u‖²_{H²}<∞`，含 Appendix A 的 **Galilean 均值消去**与 `ν` 重标度；实例化 HeliCorgi 抽象层 | T10 | **L** | A01+A02+A04 | T01；`PeriodicOrdinaryLocal`、`PeriodicLifespan`、`PeriodicUniqueness`、`PeriodicPicard*`、`PeriodicForcedDuhamel`；目标结构体 `ClassicalPeriodicLocalTheory` |
| **T12** | 均值零场的 Sobolev 微积分与临界嵌入：`eq:Rproduct`、`‖v‖_∞≤C‖v‖_{H²}`、`‖v‖₃≤C‖v‖_{Ḣ^{1/2}}`、`‖∇v‖₃+‖Λv‖₃≤C‖v‖_{Ḣ^{3/2}}`、`‖∇v‖₆≤C‖Δv‖₂`、`‖v‖_{H²}≤C‖Δv‖₂`、谱隙 | T10 | M | A03+A05 | T01；`PeriodicCompactSobolevL6`、`PeriodicH2Embedding`、`PeriodicCriticalBridge`（有限模，不能冒充） |
| **T13** | `lem:localization`：Gagliardo 恒等式 `I_R=c_s‖·‖²_{Ḣ^s(R³)}`、`I_T=c_s‖·‖²_{Ḣ^s(T³)}`、核 `K_s`、格点尾和、`eq:localization` 常数对支撑一致 | T10 | **L** | 无（最接近 D01 齐次范数见证） | T02；`PeriodicLocalization`（vendor）、`PeriodicBridge`、`TorusCube` |
| **T14** | 包导入 + 能量：`thm:packet` 接口、`lem:packetenergy`（`M`、`D`、`eq:packetenergy`、初始区间为零、负时间光滑零延拓） | T10 | S–M | U01+I01（复用已注册的 `I01.packet`） | T01/T02；`Section4/I01/` |
| **T15** | `prop:scaling`：`eq:packetEscale/Fscale`（`α(p,q)`）、`eq:packetHs`（经 T13）、`T` 处速度无界、压力规范、单拷贝周期化 | T13,T14 | M | I03（复用 `I03.scaling` 的欧氏恒等式） | T02；`PeriodicScalingBounds`、`ScalingLimits`、`PeriodicPacketEndpointRates` |
| **T16** | `lem:potential`：径向向量势 `∇×A=v`、光滑 Urysohn 截断、`w_ε=−∇×(η_εθ_εA)` 光滑无散周期、`eq:bgzero` | T10 | M | I02 前半（R³ 证明逐字可用） | T02；`RadialPotential`、`LocalCutoff`、`PeriodicConstantLocal` |
| **T17** | `lem:correction`：固定柱面上一致光滑的重标度轮廓 ⇒ `eq:derivativebounds`、`eq:wE`、`eq:Hmixed`，`eq:HHs` 经 T13 | T16,T13 | **L** | I02 后半 | T02；`Correction*`（7 个）、`PeriodicCorrectionEndpointRates` |
| **T18** | `thm:insertion`：`eq:insertion` 分解、两个交叉输运项恒为零、`g_ε∈F_T`、寿命恰为 `T`（T11 唯一性 + `H²↪L^∞`）、`eq:Eclose/Fclose/Hsclose` | T11,T14,T15,T16,T17,T12 | **L** | R42（同一证明骨架） | T02；`PeriodicInsertion*`（7 个）、`PeriodicCrossComponentTransport*` |
| **T19** | 密度包：`prop:density`（两分法）、`cor:mixed`（`3/p+2/q>3`）、`cor:closure`、`prop:projection`（`∀a∃f`） | T18,T11 | M | R41 正向 + R46 闭包半 | T03；`PeriodicDense`、`PeriodicDensityDichotomy`、`PeriodicDensityFiber` |
| **T20** | `prop:critical`：均值消去（`m'=ḡ`、`eq:meanbound`、`eq:meanfree`、常输运的反自伴/与乘子交换）、`eq:criticalenergy`、`eq:bintegral`、bootstrap `eq:ybound`、`eq:H1energy`、经 `eq:criterion` 延拓 | T10,T11,T12 | **L** | R43 + C01 + A04 | T03；`PeriodicCriticalRegularity`、`CriticalEnergy*`（5 个）、`PeriodicMeanZeroEstimate`；目标结构体 `CriticalRegularityCertificate` |
| **T21** | `cor:nondensity` + `thm:main` (i)+(ii) 装配；开球 `{‖g‖_{L¹_tH^{1/2}}<cν}`、单调性 `‖·‖_{H^{1/2}}≤‖·‖_{H^s}` | T19,T20 | S–M | R41 装配 | T03；`PeriodicMain`、`ManuscriptTopology` |
| **T22** | 有界区域层：`eq:restriction-norm`、`eq:zero-extension`（`H^s(R³)` 乘子界，常数与 `ε` 无关） | T10 | M | D01 式范数记账（角色近 R47） | T04；`BoundaryAnalyticBridge`、`BoundaryReferenceRestriction` |
| **T23** | `cor:boundary`：内部无滑移插入、边界领保持、区域 vs 零延拓范数、无滑移唯一性 | T18,T22 | M–L | 无（结构像限制到 Ω 的 R42） | T04；`BoundaryCorollaryCorrected`（先处理 `BoundaryCorollary.lean:90` 的 sorry） |
| **T24** | 其他构造：`prop:affine`、`prop:multiple`、`prop:conservative`（三条独立叶子，可拆成 T24a/b/c） | T14,T15 | M | 无（I01/I03 的叶子推论） | T04；`ConservativeForce`、`PeriodicNonpositiveForce` |

**关键路径**：`T10 → T11 → T18 → T19 → T21`（T11 是最大风险，正如 A01 在 R³ 侧）。**从一开始就可并行的叶子**：T13（局部化）、T16（向量势）、T22、T24c（保守力）——都只依赖 T10。**障碍脊柱 `T12 → T20 → T21` 与整条构造脊柱独立**，可同时配人。

## 4. 阈值与"更简单"的具体兑现

| 量 | 第 3 节 | 第 4 节 |
|---|---|---|
| 临界阶 | `s_c = 1/2`，只有 `q=1` | `s_q = 2/q − 3/2`，`q∈{1,2}` |
| 包力率 | `‖F_ε‖_{L¹H^s} ≤ C(ε^{1/2}+ε^{1/2−s})`，`0≤s≤1` | `eq:RpositiveScale/RnegativeScale` |
| 负阶 | 平凡：`‖z‖_{H^s}≤‖z‖₂` | 需 `eq:RnegativeScale` + 单调性技巧 |
| 小性常数 | `c` 只依赖单位环面与范数约定 | Prop 4.4 的 `r_{ν,S}` 依赖 `S` |
| 不需要的 | eq:RL2 低频估计、`q=2` 临界估计、B01/B02 完备化、Helmholtz/径向势压力恢复 | — |

## 5. 并行/串行安排（等第 4 节收尾后启动）

**阶段 S3-0（准备，1 条 lane，串行）**：T10 的合同**双盲陈述**（规则 2）+ 表示层桥：把 `PeriodicSobolev*`/`PeriodicHeatMultiplier`/`PeriodicLeray*` 的系数侧接口整理成 `Contracts/V1/TorusData.lean`（`IsPeriodicDatum`、`periodicSobolevENorm`、均值零子空间、Leray）；注册 `T01.torus_data` v1。同时把 `BoundaryCorollary.lean:90` 的 sorry 移出 umbrella 或修掉（MAINT）。

**阶段 S3-1（4–5 条并行）**：T13 局部化（L，astra）、T16 向量势（M，sol）、T12 均值零嵌入（M，astra；一致 `H^{1/2}↪L³` 是真正的分析核心）、T14 包能量（S，sol）、T22 有界区域范数层（M，sol）。互不依赖。

**阶段 S3-2（2 条串行主线 + 并行叶子）**：主线 A：T11 局部理论（L，astra；实例化 HeliCorgi 抽象层 + Galilean 均值消去，拆成 3–4 条小 lane：均值消去引理、T³ Stokes/Leray 实例、Picard/唯一性/重启实例、延拓判据）；主线 B：T20 临界正则性（L，astra；拆：均值消去与反自伴、临界能量恒等式、bootstrap、`H¹` 吸收与延拓）。并行叶子：T15 缩放（T13 后）、T17 修正（T13、T16 后）、T24a/b。

**阶段 S3-3（装配）**：T18 插入（L）→ T19 密度包（M）→ T21 主定理装配（S）；T23 边界推论（T18、T22 后）。

**每条 lane 的形态与第 4 节完全一致**：一个 worktree、一份自包含简报（目标陈述逐字、可满足性规则、门禁、四段报告）、codex 证明 + codex 审稿 + lead 合入链；关键路径的分析核心（T12 嵌入、T11 局部理论、T13 局部化、T20 临界）放 gpt-6-astra。

## 6. 台账与编号（与第 4 节隔离）

- 节点 ID `T10–T24` 挂到 `formalization/blueprint/tasks.json` 的 `T01–T04` 桶（`manuscript_labels` 已在桶上），`collaboration/work_items.json` 里新增对应条目时 `state: deferred → ready` 只在第 4 节 R41 装配落地后翻转；lane 序号继续全局递增（不与第 4 节抢号），PR 标题 `[NNN-T1x]`。
- 合同 id 前缀 `T01.`/`T02.`/`T03.`/`T04.`（`parent_task` 用桶），版本从 v1 起；`Contracts/V1` 冻结规则同样适用。
- 外部协作者可领的纯分析包（不碰主线）：T13 局部化、T12 一致均值零嵌入、T22 有界区域层、T24a/b/c——写进 `HANDOFF.md` 的下一版（lane 号 300–399 留给第 3 节外部协作）。

## 7. 风险与不做的事

- **不用** `NSFormalization/Citations/` 的 6 个占位公理；**不用**有限模常数冒充一致嵌入（T01 合同明令）。
- T11 与 T20 都要经过均值消去；先在 T10 里把"均值零子空间 + 常输运 `m(t)·∇` 与 Fourier 乘子交换、`L²` 反自伴"做成一个小合同，两条主线共用。
- `lem:localization`（T13）没有第 4 节对应物，是真正的新分析，但它一旦落地就把 I01/I02/I03 三个已注册合同转成环面陈述——优先级仅次于 T10。
- 如果 T11 的 HeliCorgi 实例化不顺（其 `EndpointSafeTwoSpace*` 的两空间契约需要 T³ 的 Stokes 平滑 `H²→H³`），退路是同型复制第 4 节 A01 的柱面路线到系数级——论证结构（Horizon、HasAprioriBound、因果窗口唯一性、基阶半径先验界族）已经在本仓库验证过一遍。
