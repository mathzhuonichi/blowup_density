# NEXT_SESSION.md — 当前状态与下一步

更新：2026-09-13（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状

- 本地 `main` 已与 `origin/main` 同步（owner 于 09-13 把默认分支改成 `main`，旧 `codex/*` 分支已删）。
- Lean 环境自包含装好：`bash scripts/lean-install.sh` 幂等，`make test`、`make check` 都绿
  （唯一合同 `R41.threshold_arithmetic`，标准 3 公理）。每个 shell 先 `. scripts/lean-env.sh`。
- 未提交的本地改动：`.gitignore`（加 `.env`）、`CLAUDE.md`、`NEXT_SESSION.md`、`PLAN.md`、`scripts/`、
  `logs/AGENT_RUNS.csv`（只有表头）、`reference/Cao_Chi_2026_arXiv_2609.10262v1_Torus_Paper1.pdf` + `reference/README.md` 一段登记。
- 本地不提交：`.claude/agents/prover.md`（钉 Opus 4.8），已写进 `.git/info/exclude`。
- OpenAI 包核实：Theorem 1.1 在 Lean 里完整（`formalization.yaml` sorry 0；主定理
  `NavierStokes.Comparator.navier_stokes_breakdown_R3`，标准 3 公理）。第 4 节可直接以它为输入。
- 外部候选代码 `awkronos/navier`（OpenAI 构造的独立 Lean 重做，4.31.0，MIT）对 A01/A02/A04 无现成帮助，只做对照。
- `model: opus` 的 subagent 自报 Opus 5（1M）。Opus 4.8 需通过 `prover` agent 定义，**重启会话后才加载**。

## 下一步（按顺序）

1. **重启会话**，起一个 `prover` subagent 自报型号，确认 4.8 可用；不可用就在 `CLAUDE.md`/`PLAN.md` 改成 opus 默认。
2. 开分支 `erenup/setup-claude-md`，把上面的本地改动提 PR（需 owner review）。
3. 按 `PLAN.md` 第 4 节开 5 条 lane（各自 worktree + claim PR）：
   D01 定义、U05 工具链、I01 packet 能量、A05 嵌入 spec、陈述 BFS（R41→R47 草案）。
4. 每条 lane 的陈述先走"2 个只读论文的 agent 各写一版 → 比对 → 差异写任务卡"，再动证明。

## 待 owner 决定

- 是否接受 `CLAUDE.md` / `NEXT_SESSION.md` / `PLAN.md` / `scripts/` / `logs/AGENT_RUNS.csv` 进仓库（否则留本地分支）。
- 陈述保真比对若与论文有出入，只记 `logs/`，不动 `paper/`。
