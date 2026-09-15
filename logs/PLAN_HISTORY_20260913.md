# PLAN.md 历史片段（2026-09-13 版的 §4/§5，2026-09-15 整理时原文搬出）

以下两节是 2026-09-13 的并发安排与模型预算，已被 `PLAN.md` §6 取代；原文保留在此，不再维护。

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

