# NEXT_SESSION.md — 当前状态与下一步

更新：2026-09-13（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状（2026-09-13 清晨，第二波进行中）

- 分支模型：根目录停在干净的 `main`；集成分支 `erenup/integration`（worktree `.claude/worktrees/000-integration`，Lean 环境已装、全绿）。
- 已合入 integration（PR #4–#17）：001 setup、002/003 D01 草案、004 U05 探针、005 I01 spec、006/012 台账 v1/v2、
  **007 `I01.packet` 合同**、008 I02 spec、**009 `Contracts/V1/Data.lean`（63 定义）**、**010 HeliCorgi 88 模块移植**、013 A01 spec + 路线备忘、014 A05 spec。
- 进行中：011 I02 合同+证明（最重）、015 I03 spec 修正（reviewer 的 HIGH：scalingStatement 量化过宽）。
- draft PR **#15** integration → main 已开。CI 曾因 25 分钟超时失败（`lake test` 在 2 核 runner 上要从头编 I01.packet 的 534 个本地模块）；
  已改 `.github/workflows/contracts.yml`：超时 90 分钟 + 缓存本仓自己的 olean（actions/cache 按 commit 钉）。**CI 跑期间不要 push integration**（cancel-in-progress）。
- 关键结论已入库：A01 路线 = OpenAI/本地 forced Duhamel 主干 + HeliCorgi 压力，真正缺的是"阶数 m 的 continuation + 跨阶一致"（A2b）；
  A05 的 L⁶ 界几乎现成、L^{p_a} 嵌入差 (2π)^{-a} 约定搬运；I03 的负阶缩放源码全覆盖，R46 阻塞在"缩放场的齐次范数界"（U7c）。
- 三条流程教训在 CLAUDE.md：Lake 无 `-j`；合同 import 精确白名单；任务卡是生成的，Attempts 放 `research/<ID>/ATTEMPTS.md`；CI cancel-in-progress。

## 下一步

1. 收 011 → reviewer → 合入（第二条 PDE 合同 `I02.correction`）。收 015 修正 → 合入。
2. CI 绿后把 PR #15 标 ready，请 owner review（正文列了 5 项待批：import 白名单、defaultTargets、snapshot、DAG 提案、CI 超时/缓存）。
3. 第三波（编号从 016 起）：A02 spec（唯一性/最大解，依赖 A01 spec）、B01/B02 spec、A03 spec（tame 积，R42 也需要）、I03 合同、A05 合同（先做 L⁶ 那条）。

## 待 owner 决定

- `erenup/integration` → `main` 的第一个 PR 何时提（建议：D01 定稿 + U05 报告出来后）。
