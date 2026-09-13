# PLAN.md — 第 4 节 Lean 证明的总体计划

更新 2026-09-13。状态看 [`NEXT_SESSION.md`](NEXT_SESSION.md)，规矩看 [`CLAUDE.md`](CLAUDE.md)。
本文件在每次 PR 合入后更新"进度表"一节，其余部分只在计划变更时改。

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

## 4. 并发安排（5 条 lane）

| 波次 | lane 编号 | 节点 | 说明 |
|---|---|---|---|
| 1（进行中） | 002 / 003 | D01 定义草案 A / B | 两个互不可见的 agent，lead 比对后定稿 |
| 1 | 004 | U05 工具链探针 | HeliCorgi 模块在 4.34.0-rc2 下试编 |
| 1 | 005 | I01 packet 能量 spec | 只依赖 OpenAI 包 |
| 1 | 006 | SPEC 第 4 节陈述台账 | R41→R47 自顶向下 BFS，产出 D01 需求清单 |
| 2 | 007+ | A01（2 条：存在性、正则性）、A05、I02、B01、B02 | D01 定稿后 |
| 3 | | A02、A03、I03、G01、C01 | |
| 4 | | A04、R42、R41D | |
| 收尾 | | R43、R44、R46、R41、R45、R47 | |

编号规则见 `CLAUDE.md`；每条 lane 的 PR 以 `erenup/integration` 为 base，lead 合入；攒一批后从 `erenup/integration` 向 `main` 提 PR。

A01 单独占 2 条 lane：存在性（复用 OpenAI 的 forced Duhamel + HeliCorgi 的 R³ 算子）和
全阶正则性 / 场同定 是两块可分的工作。

## 5. 模型与预算

- lead：本会话（Fable 5.1）。只做拆任务、比对、归并、记账，不亲自写长证明。
- worker：`prover` agent（`.claude/agents/prover.md`，钉 `claude-opus-4-8`，本地未提交，`.git/info/exclude` 排除）。
  用户指定 Opus 4.8。项目级 agent 定义在会话启动时加载，本会话起不了，**下次启动先起一个 `prover` 自报型号**；
  若 4.8 不可用，退回 `general-purpose` + `model: opus`（已验证解析为 Opus 5, 1M context）。
- reviewer / spec 第二人：同上，但 prompt 里禁止看另一个 agent 的输出。
- 每个 subagent 任务限定在一个引理或一个陈述，避免长上下文漂移。

## 6. 记录与恢复（防 context 压缩）

- `PLAN.md`：全貌 + 进度表（每次合入更新）。
- `NEXT_SESSION.md`：每次收工必更新，新 session 第一件事读它。
- `collaboration/tasks/<ID>.md`：每个任务的对照表和 `## Attempts`（正负例）。
- `logs/AGENT_RUNS.csv`：每次 subagent 运行一行。
- 本地会话原始记录在 `~/.claude/projects/-data-8T-ping-blowup-density/*.jsonl`。
  细节丢失时派一个 subagent 用 grep 在里面找（关键词：任务 ID、引理名、文件名），不要整文件读进主上下文。

## 7. 进度表

| 节点 | 状态 | 合同 | PR | 备注 |
|---|---|---|---|---|
| R41 算术部件 | 绿 | `R41.threshold_arithmetic` V1 | #1 | owner 提交，只含算术 |
| 001-MAINT-setup | 已合入 integration | — | #4 | CLAUDE.md / PLAN / scripts / .gitignore |
| 002-D01a-definitions | 已合入（REJECT 留档） | — | #7 | 草案 A 漏了 F_R 的 C^∞ 条件 → 定理 4.1(ii) 变假；归并 lane 修 |
| 003-D01b-definitions | 已合入（ACCEPT-WITH-NOTES） | — | #9 | 草案 B 带 C^∞；major：CompletedDense 量词过宽；归并基底 |
| 004-U05-toolchain-probe | 已合入（ACCEPT-WITH-NOTES） | — | #8 | 88 模块闭包 84 过、1 错（NNReal.mk）、3 阻塞；reviewer 实测 srcDir+roots 方案可行 |
| 005-I01-packet-energy | 已合入（ACCEPT-WITH-NOTES） | — | #5 | 27 字段 PacketAPI；11 条是 OpenAI 直接投影 |
| 006-SPEC-section4-statements | 已合入（ACCEPT-WITH-NOTES） | — | #6 | 1175 行台账；DAG 修正建议见下 |
| 007-I01-contract | 已合入（ACCEPT-WITH-NOTES，已修） | **`I01.packet` V1 已注册** | #12 | 第一条 PDE 合同；27 义务全证；20 个内联定义 + 19 个 rfl 桥；标准 3 公理 |
| 008-I02-correction-spec | 已合入（ACCEPT-WITH-NOTES） | — | #10 | 76 字段 CorrectionAPI；3.4/3.5 的 R³ 内容本地已基本证完，缺 4 小项 |
| 011-I02-contract | 已合入 | **`I02.correction` V1 已注册（rebase 后门禁全绿）** | #19 | 73 义务全证；范数已搬到 Data.lean 的 ℝ≥0∞ 规范范数；多一条论文自带的假设 π 光滑；参考解开板光滑桥因单切片消失 |
| 016-A02-spec | 已合入 | — | #22 | ACCEPT-WITH-NOTES 已修（压力基点归一化字段；U1 拆成 M+L）；本地 `classical_uniqueness_on_Icc` 同载体；加边 A03 → A02 |
| 017-A03-spec | 已合入 | — | #20 | ACCEPT-WITH-NOTES 已修；标量理论本地已完整，缺实向量/张量层与实性稳定性；U2 依赖 D01 L2（风险） |
| 018-B01-spec | 已合入 | — | #21 | ACCEPT-WITH-NOTES 已修；主字段已由本地源码覆盖（所有 s、q<∞）；缺口只剩时间 C^∞ 搬运；无 L 单元 |
| 012-SPEC-ledger-fixes | 已合入 | — | #13 | 台账 v2：12 处修正 + DAG 提案 + CHANGELOG |
| 010-U05-port | 已合入（ACCEPT-WITH-NOTES） | — | #11 | 88 模块全部编过；补丁只在 4 个副本、1 处 have；vendor 零改动；make snapshot 待 owner 重拍 |
| 009-D01-reconcile | 已合入（ACCEPT-WITH-NOTES，已修） | **`Contracts/V1/Data.lean`**（定义合同，不注册） | #14 | 63 个定义；**合同 import 精确白名单 6 本地 + 1 上游模块，待 owner 批准** |
| 013-A01-spec | 已合入 | — | #17 | ACCEPT-WITH-NOTES 已修；路线：OpenAI/本地 forced Duhamel 主干 + HeliCorgi 压力；缺的关键单元是阶数 m 的 continuation + 跨阶一致（A2b）；15 单元 3S/7M/5L |
| 014-A05-spec | 已合入 | — | #16 | ACCEPT-WITH-NOTES 已修（端点 3/2）；L⁶ 界几乎现成；L^{p_a} 骨架需搬约定（(2π)^{-a}）；Λ 做关系 |
| 015-I03-spec | 已合入 | — | #18 | ACCEPT-WITH-NOTES 已修（scalingStatement 补 7 条前提可满足；Prop 3.3 转运 3 字段）；U7c 是 R46 阻塞点 |
| 019-A05-l6-contract | 已合入 | **`A05.gradient_l6` V1 已注册** | #23 | 论文原形；Hessian–Laplacian 等式；无 Fourier；R43/R44 消费它还需 datum ⇒ jets + 时间切片提取（下一条 D01 lane） |
| 020-D01-hm-datum | 已合入 | — | #24 | **已证** jets ⇒ datum，任意实数阶、无紧支撑；29 定理标准公理；ACCEPT-WITH-NOTES 已修；余：datum ⇒ jets、双边范数、时间路径 |
| 021-I03-contract | 已合入 | **`I03.scaling` V1 已注册** | #26 | 31 字段全证（等式处证等式；力收敛 q=1,2）；HomogeneousScalingAPI 未注册；定理 4.2 不依赖齐次界，R46 只卡 U7c |
| 022-B02-spec | 已合入 | — | #27 | 20 字段；范围 −3/2 < s ≤ 0；常数经 reviewer 独立推导一致；齐次实现半边为空（单元 6 = U7c，XL，建一次共用） |
| 023-A03-l2linf-contract | 已合入 | **`A03.bounded_representative` V1 已注册** | #25 | H² jet 形式，逐点 + ess-sup；复用 OpenAI `smooth_pointwise_le_H2`；datum 形式待 D01 反向 |
| 024-D01-homogeneous-witness | ACCEPT-WITH-NOTES 已修，已合入 | — | #28 | **已证**：Schwartz/C_c^∞ 场在所有 s > −3/2 有齐次数据 + 范数恒等式；任意实数阶唯一性（L7）；差分；路径提升缺强可测；56 声明标准公理；发现 B02 `homogeneousDatumSub` 原样为假 |
| 025-D01-datum-to-jets | ACCEPT，已合入 | — | #29 | **已证**：`MemHInfty ↔ SmoothSquareIntegrableJets`、定量 jet 界（一个 (2π)^m）、含 t=0 的切片提取、`MemHInfty` 导数封闭；两条 jet 合同已从 `ClassicalSolutionR` 端到端应用成功；L2 全部关闭 |
| 026-A03-tame-contract | ACCEPT-WITH-NOTES 已修，已合入 | **`A03.tame_products` V1 已注册** | #31 | datum 层：eq:Rproduct(1)、eq:algebra、eq:tame（H² 低阶因子）、差分、对流；新证实子空间在完备乘法下稳定；3 字段待 datum⇒jets（025）后补；8 处 maxHeartbeats 待 reviewer 评估 |
| 027-R42-assembly-contract | ACCEPT 已修，已合入 | **`R42.insertion_family` V1 已注册（第 7 条）** | #30 | 定理 4.2 除寿命同定外全部子句；K→K_* 在 R42 侧以缩小 ε₀ 解决；**缺口：无合同提供 g_ε ∈ F_R（时间正则性）**，连寿命 ≥ T 都无法陈述 → 028 |
| 028-D01-forceclass-closure | ACCEPT，已合入 | — | #32 | **已证**：F_c ⊆ F_R（datum 路径时间 C^∞）、F_R/F_c 加法封闭、g+H_ε+F_ε ∈ F_R（R42 可直接消费）；23 定理标准公理；余：u_ε 的 `ClassicalSolutionR.sobolev`（非紧支） |
| 029-I02-v2-thetaradius | ACCEPT，已合入 | **`I02.correction_v2` 已注册** | #33 | `extends` V1 + 1 字段 `K ⊆ plateau`；兼容绑定 V1-of-V2；`force_carrier_subset_ball` 直接证出 021/027 说"无法履行"的前提；政策脚本零改动 |
| 030-A04-spec | ACCEPT-WITH-NOTES 已修，已合入 | — | #35 | 平方 H² continuation 适配器（∫‖u‖²_{H²} < ∞ ⇒ 高阶界 + 越过 S 的一致重启；R43/R44 的关键路径） |
| 031-C01-spec | ACCEPT-WITH-NOTES 已修，已合入 | — | #36 | 常规能量与 H¹ 吸收（eq:RL2、eq:RH1；R43/R44 用） |
| 032-A02-restrict-order | ACCEPT-WITH-NOTES 已修，已合入 | — | #34 | A02 单元 U4+U6：`restrict`/congruence/`pressure_normalization` 与六个序论字段（无分析） |
| 033-A02-energy-u1a | ACCEPT-WITH-NOTES，已合入（去重 → 040） | — | #38 | A02 单元 U1a：`ClassicalSolutionR` ⇒ `UniformFiniteEnergy (Icc 0 T')` |
| 034-D01-lemma-contract | ACCEPT-WITH-NOTES 已修，已合入 | **`D01.datum_lemmas` V1（第 10 条）** | #37 | 把 020/024/025/028 的 D01 引理收成合同 `D01.datum_lemmas`（jets⇔datum、齐次见证、F_R 闭包、切片提取），进 `make test` 闭包 |
| 035-B01-units-1-3 | ACCEPT-WITH-NOTES 已修，已合入 | — | #39 | B01 单元 1–3（R46 实际消费的三条：Schwartz/紧支稠密 + 完备化代表元），`Section4/B01/` |
| 036-B02-units-3-4 | ACCEPT-WITH-NOTES，已合入 | — | #42 | B02 单元 3+4（低频权重可积性/积分值；角 Fourier 上确界界），`Section4/B02/` |
| 037-R43-spec-A | 盲稿 A+B 比对调和完成，已合入 | — | #40 | `RCritical1API` 4 字段（B 形状）；上游缺口 G1–G7 见 `research/R43/COMPARISON.md` §4 |
| 038-R43-spec-B | 已合入（经 037） | — | #40 | 命题 4.3 spec 盲稿 B（与 037 互不可见） |
| 039-A04-units-f1-n1 | ACCEPT-WITH-NOTES 已修，已合入 | — | #41 | A04 单元 F1（`MemForceR` ⇒ L¹_tH^m / 有界 H¹ 力）+ N1（被积函数连续性），`Section4/A04/` |
| 040-SIMP-A02-dedupe | ACCEPT-WITH-NOTES，已合入 | — | #43 | A02 四模块的 simplifier + tester：Restrict §0 → import SolutionClass；Energy §1–2 → D01 DatumToJets；conformance/negative 检查 |
| 041-A04-unit-g3 | ACCEPT-WITH-NOTES 已修，已合入 | — | #45 | A04 单元 G3：连续变系数 Grönwall（纯 ODE 引理，Mathlib 缺），`Section4/A04/Gronwall.lean` |
| 042-D01-halforder-force-norms | ACCEPT-WITH-NOTES，已合入 | — | #44 | D01 G3+G2：`MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤`（及齐次孪生）、路径级 Ḣ^{1/2} ≤ H^{1/2}；`Section4/D01/HalfOrder.lean` |
| 043-A04-unit-z1 | ACCEPT-WITH-NOTES 已修，已合入 | — | #46 | A04 单元 Z1：带线性项的 ζ-正则化开方微分不等式（推广 `Paper1.sqrt_energy_le_primitive`），`Section4/A04/Regularized.lean` |
| 044-C01-unit-u6 | ACCEPT-WITH-NOTES 已修，已合入 | — | #47 | C01 单元 U6（无 U1 依赖）：L³ 插值 + `laplacianSqENorm` 桥，`Section4/C01/` |
| 045-C01-unit-u2 | ACCEPT-WITH-NOTES，已合入 | — | #48 | C01 单元 U2：`MemForceR f ⇒ MemLp (slice f t) 2` + `t ↦ ‖f(t)‖₂` 连续（`forceTimeRegularity`），`Section4/C01/ForceSlices.lean` |
| 046-R44-spec-A | 盲稿 A+B 比对调和完成，已合入 | — | #49 | `RCritical2API` 9 字段；缺口 G1（J 权重恒等式）、G2（eq:Rcritical2）、G3（H^{-1/2} 力切片）、G5（幂拼写）见 `research/R44/COMPARISON.md` §4 |
| 047-R44-spec-B | 已并入 046 | — | — | 命题 4.4 spec 盲稿 B（与 046 互不可见，同样输入） |
| 048-B01-units-6-8 | ACCEPT-WITH-NOTES 已修，已合入 | — | #51 | B01 单元 6（`separatedAssembly`）+ 8（`spatialApprox`），`Section4/B01/Separated.lean` |
| 049-A02-unit-u1b | ACCEPT，已合入 | — | #50 | A02 单元 U1b：`ClassicalSolutionR` 在 `Icc 0 T'` 上的 `‖u‖` 与 `‖∇u‖` 一致上界（经 `D01.datum_lemmas` + `A03.bounded_representative`），`Section4/A02/Bounds.lean` |
| 050-C01-units-u1-u3 | ACCEPT-WITH-NOTES 已修，已合入 | — | #52 | C01 单元 U1（`velocityJets`，经 `D01.datum_lemmas` 现为 S）+ U3（演化打包成 `SmoothL2Field` 路径），`Section4/C01/{VelocityJets,Evolution}.lean` |
| 051-B02-unit-1 | ACCEPT-WITH-NOTES 已修，已合入 | — | #56 | B02 单元 1：环形截断 + 光滑化（`annularRestriction`、`annularSmoothing`），`Section4/B02/Annular.lean` |
| 052-A02-units-u2-u3 | ACCEPT，已合入 | — | #53 | A02 单元 U2（`velocity_unique` 经 `classical_uniqueness_on_Icc` + U1a + U1b）+ U3（`pressure_gauge`）；**叠在 049 分支上**，`Section4/A02/Uniqueness.lean` |
| 053-A04-unit-d1 | ACCEPT-WITH-NOTES 已修，已合入 | — | #54 | A04 单元 D1：`HasSmoothSobolevPath` ⇒ 平方 datum 范数的导数 `2⟪G t, G' t⟫`，与 `sobolevNormAt = ‖G‖`；**叠在 039 分支上**，`Section4/A04/DerivNorm.lean` |
| 054-D01-datum-lemmas-v2 | ACCEPT-WITH-NOTES 已修，已合入 | **`D01.datum_lemmas_v2`（第 11 条）** | #55 | `D01.datum_lemmas` **V2**：`extends` V1 + 042 的 `forceSobolevENorm_ne_top` 字段；Bindings import `HalfOrder`（进合同闭包） |
| 055-D01-unit-l9c | 进行中 | — | — | D01 单元 L9(c)：eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` 与压力梯度的全阶 jet（C01 U4/U7 的根缺口），`Section4/D01/Pressure.lean` |
| 056-A04-g1-split | 进行中 | — | — | A04 单元 G1（forced viscous eq:Rhigh 在 datum 载体上；= A01 A2）的 spec 级拆分：给定 D1/D2/动量/tame 积，列出子引理与精确陈述，证能证的 S 级子步 |
| 057-A02-uniqueness-contract | 进行中 | — | — | 注册 `A02.uniqueness`（`UniquenessAPI`：`velocity_unique` + `pressure_gauge`，绑定 052/049/033 的定理，`ClassicalSolutionR` 逐字段桥） |
| 058-A02-units-u5-u9 | 进行中 | — | — | A02 单元 U5（`patch`，取更长 horizon）+ U9（`lifespan_le_of_unbounded`，经 U1b 的 H² 上界机制），`Section4/A02/Patch.lean` |
| 059-B02-unit-7 | 进行中 | — | — | B02 单元 7：`lowHighSplit`（低/高频拆分，`k ∈ L¹ ∩ L²`，角坐标约定），`Section4/B02/LowHigh.lean` |
| 其余节点 | 未开始 | — | — | |

## 8. 已发现的 DAG 修正建议（待 owner，来自 006 及其 review）

- 加边 A03 → R42：定理 4.2 的"寿命 ≤ T"一步用了引理 A.1 的 H² → L^∞。
- 加边 A03 → A02：唯一性证明的 Grönwall 系数 ‖∇u₂‖_∞ 只靠 H² → L^∞ 才有限（appendix-a:120-123）；A03 的祖先闭包 {D01, U04, A05, U03} 无环。
- R41D 按外力子类（F_R / F_c / F_rd）参数化，并加边 R41D → R45；推论 4.5 和命题 4.6 都需要定理 4.2 的紧支撑修正，而不只是定理 4.1 的结论。
- R42 的合同要显式导出 u_ε − v 无散和紧支撑压力规范，定理 4.7 的证明用到；R47 允许多一个只依赖时间的常数 κ(t)。
- 定理 4.2 / 命题 4.6 / 定理 4.7 必须共用同一个 ε 族（一个线程化的见证），ε₀ 取所有约束的最小值。
- 齐次实现：一个定义 Ḣ^s = {ĥ 可测, |ξ|^s ĥ ∈ L²}（−3/2 < s < 3/2）可覆盖 4.3 / 4.2 / 4.6 三处用法，其余作引理；‖·‖_{Ḣ^{3/2}} 只需定义为量。

- **D01 需补（R43 调和发现，阻塞 R43/R44 陈述的非空洞性）**：(G3) `MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` 及齐次孪生——`MemForceR` 只给整数阶 datum 路径，半阶范数是 1/2 阶路径上的下确界，可能对所有真实 f 都是 ⊤，使小性假设空洞；(G2) 路径级 `‖f‖_{L¹_tḢ^{1/2}} ≤ ‖f‖_{L¹_tH^{1/2}}`（A05 只有空间切片版）——**042 关掉了不齐次的 G3；齐次 G3 与 G2 仍开：需要一般 H^∞ 切片的齐次 datum（乘子 |ξ|^{1/2}(1+|ξ|²)^{-1/4} 经 `weightedAngularFourier_realization`），树里只有 Schwartz/紧支的构造**；(G1) 把 datum 形式 `dotHomogeneousENorm` 提升为注册定义。
- **A04 G1 拆分（056，`research/A04/G1_SPLIT.md`）**：SL0=D1（done）、SL6/SL8（done）；阻塞：SL1=D2（`deriv G t` = ∂ₜu 的 datum，需 A01 的 C^∞_{t,x} 正则性——`HasSmoothSobolevPath` 单独不够）、SL2 动量方程 datum 形式（A01）、SL3 Laplace 恒等式（datum 侧阶移 + `gradientSobolevNormAt` 的 formalization 定义）、SL4=P2、SL5 `∇·(u⊗u)` 的 H^m 分部积分。**结论：G1 的核心就是 A01 的 datum 层正则性输出；下一步先做 A01 单元 A1/A2 的 spec 拆分，而不是继续在 A04 里堆。**
- **L9(c) 收敛为一个义务 P2（055）**：`∂ₜu(t,·) ∈ SmoothSquareIntegrableJets` ⟺ Leray 投影 `(I−P)` 在物理实场（角约定）的 H^m 上有界；HeliCorgi 港口只有 cycles 约定、复数、分布层面、零阶的 `r3LerayComplementL2`/`r3HelmholtzPressure_gradient`，桥（实线性 + 约定 + 分布↔经典 + L²→H^m）是独立单元。另：`∇p` 的 jet 无 `MemForceR f` 时**为假**（055 给出反例），所以 C01 U4/U7 必须带力项假设。
- **A04 新义务 D2（053 reviewer 发现）**：`HasSmoothSobolevPath` 只给出光滑 datum 路径 `G`，没有人断言 `deriv G t` 是 `∂ₜu(t,·)` 的 datum；G1 要用动量方程替换导数前必须先有这条（属 A01 产出路径的一部分，或 A04 自证：datum 路径的时间导数 = 时间导数的 datum，经 `IsSobolevDatum` 的唯一性 L1 + 差商极限）。
- **C01 U3 发现（050，reviewer 修正）**：能量恒等式的消费者需要 `∇p(t)` 为全阶 `SmoothL2Field`，而 `ClassicalSolutionR` 只给 `∇p` 的零阶 `MemLp` + 空间光滑。**唯一根缺口**：压力梯度 jet；时间导数由 `momentum` 代数读出（∂ₜu = f − (u·∇)u + νΔu − ∇p）。诚实修法只有一条：**椭圆正则性单元 L9(c)**（`Data.lean:621`：eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` 是类的定理不是字段；Leray 投影在每个 H^m 有界 + u⊗u 的 H^∞ 代数）。不能给 `ClassicalSolutionR` 加压力 datum 子句（会让 Lean 类比论文强、把义务推给 prop:local 的构造者）。L9(c) 原记为"卡 U05"，U05 已完成（HeliCorgi 已移植），可以开。
- **D01 定义缺口（037 发现，待 D01 V2）**：`Data.lean` 的 `dotHHalfENorm`/`dotHThreeHalvesENorm` 是逐点 Fourier 积分，对非 L¹ 的 H^∞ 场退化为 0；R43/R44/A05/C01 的 smallness 假设必须共用 datum-下确界的齐次范数（A05 的 `dotHomogeneousENorm`），否则错误实现可空洞满足。
