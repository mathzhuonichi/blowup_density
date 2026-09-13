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
| 011-I02-contract | PR #19 待合（CI 跑完） | **`I02.correction` V1 已注册（rebase 后门禁全绿）** | #19 | 73 义务全证；范数已搬到 Data.lean 的 ℝ≥0∞ 规范范数；多一条论文自带的假设 π 光滑；参考解开板光滑桥因单切片消失 |
| 016-A02-spec | review 中 | — | — | UniquenessAPI + MaximalSolutionAPI 通过检查；找到本地 `classical_uniqueness_on_Icc`（同载体）；主张需加边 A03 → A02（与台账 v2 相反，待 reviewer 裁定）；10 单元无 L |
| 017-A03-spec | PR #20 待合（CI 跑完） | — | #20 | ACCEPT-WITH-NOTES 已修；标量理论本地已完整，缺实向量/张量层与实性稳定性；U2 依赖 D01 L2（风险） |
| 018-B01-spec | review 中 | — | — | BochnerApproxAPI 通过检查；主字段已由本地 `exists_angular_real_vector_positive_physical_approx` 覆盖（所有 s、q<∞）；缺口只剩时间 C^∞ 搬运 |
| 012-SPEC-ledger-fixes | 已合入 | — | #13 | 台账 v2：12 处修正 + DAG 提案 + CHANGELOG |
| 010-U05-port | 已合入（ACCEPT-WITH-NOTES） | — | #11 | 88 模块全部编过；补丁只在 4 个副本、1 处 have；vendor 零改动；make snapshot 待 owner 重拍 |
| 009-D01-reconcile | 已合入（ACCEPT-WITH-NOTES，已修） | **`Contracts/V1/Data.lean`**（定义合同，不注册） | #14 | 63 个定义；**合同 import 精确白名单 6 本地 + 1 上游模块，待 owner 批准** |
| 013-A01-spec | 已合入 | — | #17 | ACCEPT-WITH-NOTES 已修；路线：OpenAI/本地 forced Duhamel 主干 + HeliCorgi 压力；缺的关键单元是阶数 m 的 continuation + 跨阶一致（A2b）；15 单元 3S/7M/5L |
| 014-A05-spec | 已合入 | — | #16 | ACCEPT-WITH-NOTES 已修（端点 3/2）；L⁶ 界几乎现成；L^{p_a} 骨架需搬约定（(2π)^{-a}）；Λ 做关系 |
| 015-I03-spec | PR #18 待合（CI 跑完） | — | #18 | ACCEPT-WITH-NOTES 已修（scalingStatement 补 7 条前提可满足；Prop 3.3 转运 3 字段）；U7c 是 R46 阻塞点 |
| 其余节点 | 未开始 | — | — | |

## 8. 已发现的 DAG 修正建议（待 owner，来自 006 及其 review）

- 加边 A03 → R42：定理 4.2 的"寿命 ≤ T"一步用了引理 A.1 的 H² → L^∞。
- R41D 按外力子类（F_R / F_c / F_rd）参数化，并加边 R41D → R45；推论 4.5 和命题 4.6 都需要定理 4.2 的紧支撑修正，而不只是定理 4.1 的结论。
- R42 的合同要显式导出 u_ε − v 无散和紧支撑压力规范，定理 4.7 的证明用到；R47 允许多一个只依赖时间的常数 κ(t)。
- 定理 4.2 / 命题 4.6 / 定理 4.7 必须共用同一个 ε 族（一个线程化的见证），ε₀ 取所有约束的最小值。
- 齐次实现：一个定义 Ḣ^s = {ĥ 可测, |ξ|^s ĥ ∈ L²}（−3/2 < s < 3/2）可覆盖 4.3 / 4.2 / 4.6 三处用法，其余作引理；‖·‖_{Ḣ^{3/2}} 只需定义为量。
