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
| 055-D01-unit-l9c | ACCEPT-WITH-NOTES 已修，已合入 | — | #59 | D01 单元 L9(c)：eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` 与压力梯度的全阶 jet（C01 U4/U7 的根缺口），`Section4/D01/Pressure.lean` |
| 056-A04-g1-split | ACCEPT-WITH-NOTES ×2 已修，已合入（D2 已证） | — | #61 | A04 单元 G1（forced viscous eq:Rhigh 在 datum 载体上；= A01 A2）的 spec 级拆分：给定 D1/D2/动量/tame 积，列出子引理与精确陈述，证能证的 S 级子步 |
| 057-A02-uniqueness-contract | ACCEPT-WITH-NOTES 已修，已合入 | **`A02.uniqueness`（第 12 条）** | #57 | 注册 `A02.uniqueness`（`UniquenessAPI`：`velocity_unique` + `pressure_gauge`，绑定 052/049/033 的定理，`ClassicalSolutionR` 逐字段桥） |
| 058-A02-units-u5-u9 | ACCEPT，已合入 | — | #58 | A02 单元 U5（`patch`，取更长 horizon）+ U9（`lifespan_le_of_unbounded`，经 U1b 的 H² 上界机制），`Section4/A02/Patch.lean` |
| 059-B02-unit-7 | ACCEPT-WITH-NOTES，已合入（含角约定 Plancherel） | — | #62 | B02 单元 7：`lowHighSplit`（低/高频拆分，`k ∈ L¹ ∩ L²`，角坐标约定），`Section4/B02/LowHigh.lean` |
| 060-B02-unit-8 | ACCEPT-WITH-NOTES，已合入 | — | #63 | B02 单元 8：`cutoffLebesgue` + `spatialApproxHomogeneous`（对角逼近），`Section4/B02/Cutoff.lean` |
| 061-A02-maximal-partial-contract | ACCEPT，已合入 | **`A02.maximal_partial`（第 13 条）** | #60 | 注册 `A02.maximal_partial`：`MaximalSolutionAPI` 中已证的 10 个字段（六个序论 + `restrict` + `pressure_normalization` + `patch` + `lifespan_le_of_unbounded`），`horizon_le_lifespan` 带 ⟪A01:solution⟫ 显式假设 |
| 062-D01-p2-split | ACCEPT-WITH-NOTES 已修，已合入 | — | #64 | 义务 P2（Leray 补投影在实角约定全空间 H^m 上有界）的拆分 + S 级子步：盘点 HeliCorgi 港口的 `r3LerayComplementL2`/`R3LerayRealLinearBridge`，列出实线性/约定/分布↔经典/L²→H^m 四座桥的精确陈述 |
| 063-B01-unit-7-split | ACCEPT-WITH-NOTES，已合入（#67；lead 改坏 docstring，070 热修） | — | #67 | B01 单元 7（`temporalApprox` / `SeparatedTemporalDense`，L）的拆分 + S 级子步：`dense_span_separatedLp` 在 `H := RealVectorSobolev s` 的实例化、`Submodule.span` 展开、`Lp` 商到代表元 |
| 064-A02-unit-u7 | ACCEPT-WITH-NOTES，已合入 | — | #65 | A02 单元 U7：`exists_maximal` + `maximal_unique`（以 ⟪A01:solution⟫ 为显式假设；S ↑ T_max 的有向并 + U2/U3/U4 归一化的相干性），`Section4/A02/Maximal.lean` |
| 065-A04-sl2-momentum | ACCEPT-WITH-NOTES，已合入 | — | #66 | A04 子引理 SL2：动量方程的 datum 形式（用 D2 + 钉代表元技巧把 `∂ₜu = f − (u·∇)u + νΔu − ∇p` 提升到 `RealVectorSobolev m` 的 datum 等式），`Section4/A04/MomentumDatum.lean` |
| 066-A04-sl3-laplacian | 已合并 | #73 | #73 | A04 子引理 SL3：Laplace 配对恒等式 `⟪G, datum(Δu)⟫ ≤ −‖∇u‖²_{H^m}` 在 datum 载体上（datum 侧阶移 / `∂ⱼ` 的 datum = `iξⱼ`·datum，与 P2 共用），`Section4/A04/LaplacianDatum.lean` |
| 067-D01-p2-sl7a | ACCEPT-WITH-NOTES 已修，已合入 | — | #69 | P2 子引理 SL7a：零阶 Plancherel 种子 `MemLp z 2 ⟹ ∃ A, IsSobolevDatum 0 z A`（用 059 的 `angular_plancherel`；从 `pressure_gradient` 出发给 ∇p 一个零阶 datum），`Section4/D01/OrderZeroDatum.lean` |
| 068-B02-unit-6 | 已合并 | #74 | #74 | B02 单元 6：`lebesgueHomogeneousDatum`（k ∈ L¹∩L² 在 −3/2 < s ≤ 0 的齐次 datum 存在 + 范数子句）与 `homogeneousDatumSub`，用 059 的角 Plancherel，`Section4/B02/LebesgueDatum.lean` |
| 069-A02-maximal-partial-v2 | ACCEPT，已合入 | **`A02.maximal_partial_v2`（第 14 条）** | #70 | `A02.maximal_partial` **V2**：`extends` V1 + `maximal_unique`（无条件）+ `exists_maximal`（以 A01 存在性为显式假设），绑定 064 的 `Maximal.lean` |
| 070-MAINT-hotfix-temporal | 已合入 | — | #68 | 热修 063 的 docstring（lead 手改吞掉 `-/`）；全量门禁 58 模块绿 |
| 071-B01-partial-contract | ACCEPT-WITH-NOTES 已修，已合入 | **`B01.bochner_partial`（第 15 条）** | #71 | 注册 `B01.bochner_partial`：`BochnerApproxAPI` 中已证的字段（χ 五条 + 单元 1–3、6、7、8），排除单元 9 的两条保真字段与 `SeparatedCompactDense` 打包 |
| 072-R42-lifespan-split | 已合并 | #72 | #72 | R42 剩余的寿命同定子句拆分 + S 级子步：用已注册的 `A02.maximal_partial`（`lifespan_le_of_unbounded`、`lifespan_ge_of_forall_shorter`）把定理 4.2 的 `T_max(u_ε) = 1` 拆成「包的 L^∞ 爆破 ⇒ ≤ 1」与「每个 S<1 上有解 ⇒ ≥ 1」，列出缺的 `sobolev` 字段（非紧支 u_ε）与 `hg : MemForceR g` |
| 073-D01-p2-sl3-multiplier | 已合并 | #77 | #77 | P2 子引理 SL3：Leray 补投影的算子值 L² 乘子 CLM（HeliCorgi `R3LerayPointwiseL2` 模板 / `holderL` 取算子值 E），范数 ≤ 1，a.e. 作用，保实（SL2），`Section4/D01/LerayMultiplier.lean` |
| 074-D01-p2-sl4a-div | 已合并 | #75 | #75 | P2 子引理 SL4α：经典解的 `div ∂ₜu(t,·) = 0`（`∂ₜ` 与 `div` 交换 + `divergence`），以及 `∂ₜu(t,·)` 的零阶 datum 横截（`⟪ξ, Â(ξ)⟫ = 0` a.e.），`Section4/D01/DivergenceTime.lean` |
| 075-R42-correction-path | 已合并 | #79 | #79 | R42 子引理 1e-i：修正 `w_ε + U_ε`（时空光滑、空间紧支）的 datum 路径在时间上连续（`D01.contDiff_angularPath` + 时间截断 + L1 唯一性），从而 `u_ε = v + (w_ε+U_ε)` 的 `sobolev` 字段由 `reference.sobolev` + 可加性得到，`Section4/R42/CorrectionPath.lean` |
| 076-A04-sl3-pairing | 已合并 | #78 | #78 | A04 SL3 配对：`⟨Δ_datum, ·⟩ = -‖∇‖²`，经 `angularFrequencyDilation` 酉性 (`inner_map_map`) 与 066 的符号事实 (`mid_symbol_imaginary`, `mid_symbol_order_independent`)，`Section4/A04/LaplacianPairing.lean` |
| 077-SIMP-C01 | 已合并 | #76 | #76 | C01 四个已合模块的 simplifier+tester（陈述逐字不变；负向检查；conformance examples；CI 闭包） |
| 078-B02-unit-2-split | 已合并 | #80 | #80 | B02 单元 2 `annularSchwartz`（L）拆分起步：`|ξ|^{-s}·g` 在环上光滑紧支（SL1）、Schwartz 逆角 Fourier（SL2）、实值性（SL3）、组装到 `IsHomogeneousSliceDatum`（SL4）；`research/B02/U2_SPLIT.md` + `Section4/B02/AnnularSchwartz.lean` |
| 079-D01-p2-sl4-transverse | 已合并 | #85 | #85 | P2 SL4 Fourier 横向形式：无散 `SmoothL2Field` 的任一 (m+1) 阶 datum 满足 a.e. `∑ⱼ ξⱼ Âⱼ(ξ) = 0`（经 066 `isSobolevDatum_partialDeriv` + 标量 datum 唯一性 + 符号消去），再推论到 `∂ₜu(t,·)`（D2 + 074 SL4α + `A05.SmoothL2` 包装），`Section4/D01/Transverse.lean` |
| 080-R42-blowup-esssup | 已合并 | #81 | #81 | R42 子项 2a：逐点 `SpeedUnboundedAt T u` + 切片连续 ⇒ `limsupLeft T (speedENorm (u(t,·))) = ⊤`（开集正测度 ⇒ essSup 下界；limsup=⊤ 的 frequently 刻画），`Section4/R42/BlowupEssSup.lean` |
| 081-D01-p2-leray-datum | 已合并 | #82 | #82 | P2 SL3 收尾：把 073 的 `lerayComplementL2` 重打包成 datum 载体上的 `lerayComplement m : RealVectorSobolev m →L[ℝ] RealVectorSobolev m`（`coordinates ∘ lerayComplementL2 ∘ assemble` + `codRestrict` 到实子空间），范数 ≤ 1、幂等、a.e. 作用、横向为零，`Section4/D01/LerayDatum.lean` |
| 082-A04-sl3-real-pairing | 已合并 | #84 | #84 | A04 SL3 步骤 3a：实载体 `RealSobolevHilbert` 上的反自伴 `⟪f, D_a g⟫_ℝ = -⟪D_a f, g⟫_ℝ`（`angularDirectionalDerivativeReal`，实 `L2.inner_def`）、降阶配对 `⟪Λ⁻¹w, Λw⟫ = ‖w‖²`、降阶符号只依赖 r−s，`Section4/A04/RealPairing.lean` |
| 083-R42-pressure-gradient | 已合并 | #83 | #83 | R42 子项 1f：`∇p_ε = ∇π + ∇P_ε ∈ L²`（参考压力梯度 L² + 修正压力空间紧支光滑 ⇒ 梯度 L²，`MemLp.add`），`Section4/R42/PressureGradient.lean` |
| 084-B02-unit-2-sl3 | 已合并 | #86 | #86 | B02 单元 2 SL3（M）：由 datum 的共轭反射对称得 `angularFourier (postcompCLM ofRealCLM (ψ i)) =ᵐ G i`（`ψ i` = `φ i` 的实部），加 SL4a（slice distribution）与 SL4b（可积性），`Section4/B02/AnnularReal.lean` |
| 085-D01-p2-sl7c-commute | 已合并 | #89 | #89 | P2 SL7c：`lerayComplement` 与降阶 `lowerDatum` 交换（复符号 0-齐次 + 与 `angularFrequencyDilation` 交换 + 标量权交换），推论：各阶 datum 的 Leray 补由 0 阶决定，`Section4/D01/LerayLowering.lean` |
| 086-SIMP-A04 | 已合并 | #87 | #87 | A04 八个较早合入模块（Forcing, Continuity, Gronwall, Regularized, DerivNorm, HighEnergy, TimeDerivative, MomentumDatum）的 simplifier+tester（陈述逐字不变；负向检查用 `set_option autoImplicit false`；conformance；CI 闭包） |
| 087-R42-sol-on-shorter | 已合并 | #88 | #88 | R42 装配子引理 #1 `sol_on_shorter`：由 `InsertionFamilyAPI` 在每个 `0<S<T` 上构造 `ClassicalSolutionR ν a (g_ε) S`（区间收缩 + 075 `CorrectionPath` + 083 `PressureGradient` + 080 切片连续），`Section4/R42/SolutionOnShorter.lean` |
| 088-A04-sl3-assembly | 已合并 | #94 | #94 | A04 SL3 步骤 3b（M）：Laplace datum 组装 `datum_m(Δu) = ∑ⱼ D_j D_j datum_{m+2}u` + 实反自伴 + 降阶配对 ⇒ `hlap : ⟪G, L⟫ ≤ -grad²`（`A04.inner_energy_assembly` 的输入），`Section4/A04/LaplacianAssembly.lean` |
| 089-D01-p2-sl5-longitudinal | 已合并 | #91 | #91 | P2 SL5：无旋（curl-free）光滑 L² 场的任一 datum a.e. 纵向 `ξᵢ Âⱼ = ξⱼ Âᵢ` ⇒ `Â(ξ) ∈ ℂ∙ξ`（镜像 079），再 datum 层 `lerayComplement m A = A`（081 review 的 4 行），`Section4/D01/Longitudinal.lean` |
| 090-SIMP-B02 | 已合并 | #92 | #92 | B02 七个已合模块（LowFrequency, Annular, LowHigh, Cutoff, LebesgueDatum, AnnularSchwartz, AnnularReal）的 simplifier+tester（陈述逐字不变；负向检查 autoImplicit off；conformance；MAINT 清单：a.e. 共轭模式去重、`angularFourier_conj`/`angular_plancherel`/`angularFrequencyDilation_coeFn` 上提） |
| 091-C01-partial-contract | 已合并 | #90 | #90 | 注册 `C01.energy_absorption_partial`：已证的 C01 spec 字段（velocityJets, forceTimeRegularity, trilinearHolder, trilinearAbsorbed, laplacianSqENorm）逐字进 `Contracts/V1/EnergyAbsorptionPartial.lean` + Bindings + Tests + contracts.json（模板 071 `B01.bochner_partial`），把 C01 模块纳入 CI 闭包 |
| 092-R42-lifespan-binding | 已合并 | #93 | #93 | R42 寿命两子句的绑定层装配（`verification/Bindings/InsertionLifespan.lean`）：由 `InsertionFamilyAPI` + `hg : MemForceR g` + `RegularThrough ν a g (T+δ)` 得 `maximalLifespanR ν a g_ε = ofReal T` 与 `ofReal (T+δ) < maximalLifespanR ν a g`（087 + 080 + 072 + `A02.maximal_partial`），为 V2 合同铺路 |
| 093-A01-split | 审阅中 | — | — | A01（局部理论）拆分起步：对照 `research/A01/Spec.lean` 与 HeliCorgi 的 mild 存在/唯一/续接 API，写子引理表，证第一个 S 项（把 HeliCorgi 的局部解包装成 `A02.ClassicalSolutionR` 所需字段的桥），`research/A01/A01_SPLIT.md` |
| 094-D01-p2-sl7b-order0 | 进行中 | — | — | P2 SL7b-α：光滑 L² 场（不要求导数可积）的 0 阶 datum 的 a.e. 符号恒等式——无散 ⇒ 横向、无旋 ⇒ 纵向（分布导数 + `physicalDistribution_directionalField` + `OrderZeroDatum`），`Section4/D01/OrderZeroSymbol.lean` |
| 095-A04-sl5-nonlinear | 续改中 | — | — | A04 G1 SL5：非线性项的 H^m 分部积分 `⟪G, datum((u·∇)u)⟫ = -⟪∇G, datum(u⊗u)⟫`（实反自伴 082 + `derivDatumStep` 088）+ Cauchy–Schwarz ⇒ `hnl : -⟪G, N⟫ ≤ NLbound`（`A04.inner_energy_assembly` 的输入），`Section4/A04/NonlinearPairing.lean` |
| 096-R42-lifespan-contract | PR 已开 | #95 | — | 注册 `R42.insertion_lifespan`（V1 新合同，含 `family`、`memForce`、`regular` + 两条寿命子句；Bindings 用 092 的 `insertionLifespan`；Tests 公理审计 + 两条论文显示式 example + `hν`/`ha` 可导出 example），把 `Bindings/InsertionLifespan` 纳入 CI 闭包 |
| 097-B02-remaining-fields | PR 已开 | #96 | — | B02 剩余 spec 字段：`chi_*`（vendor `baseCutoff`，同 B01 绑定）、`temporalApprox`/`separatedAssembly`（B01 已证、逐字复用）、`annularPathApprox`（路径级截断，M）、`approxCompactHomogeneous`（stage 1–5 组装）；先表后证 S 项，`Section4/B02/Remaining.lean` + `research/B02/REMAINING_SPLIT.md` |
| 098-R42-full-horizon | 进行中 | — | — | R42 导出：由每个 `Ico 0 S`（S<T）上的 datum 路径经唯一性粘成 `Ico 0 T` 上的连续路径（S–M），从而 `ClassicalSolutionR ν a g_ε T`（水平线恰为 T）；A02 `IsMaximalSolution`/`insertion_lifespan_eq` 半边的表，`Section4/R42/FullHorizon.lean` |
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
