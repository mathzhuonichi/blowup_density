# NEXT_SESSION.md — 当前状态与下一步

更新：2026-09-13（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状

- 分支模型：根目录停在干净的 `main`；我们的集成分支 `erenup/integration`（worktree `.claude/worktrees/000-integration`）；
  lane PR 以它为 base，lead 自己合；攒一批后从它向 `main` 提 PR 给 owner。
- `001-MAINT-setup` 已合入 integration（PR #4；PR #3 因分支改名被 GitHub 关闭，内容相同）。
- Lean 自包含环境在每个 worktree 里都跑通（`bash scripts/lean-install.sh`，`.lake/packages` 软链到主仓）。
  D01a worktree 已预编译 `NSFormalization.Paper3.AngularSobolevClass` 闭包（8853 jobs，2.5 分钟）。
- 第一波 5 条 lane 已启动（opus subagent，各自 worktree，不提交，lead 收尾）：
  002/003 D01 草案 A/B、004 U05 探针、005 I01 spec、006 SPEC 陈述台账。
- `.claude/agents/prover.md`（钉 Opus 4.8）需重启会话才加载；本轮 worker 用 `general-purpose` + `model: opus`（= Opus 5）。

## 下一步

1. 收第一波结果：每条 lane 起一个 opus reviewer（只做：Lean 能否跑通 + 陈述与论文一致），然后 lead 提 PR to integration 并合入，记 `logs/AGENT_RUNS.csv`。
2. 比对 002 vs 003 两份 D01 草案，差异写进 `collaboration/tasks/D01.md`，定稿 `research/D01/Draft.lean` → 下一 lane 转成 `Contracts/V1`。
3. 用 006 的"D01 需求清单"校验定稿是否覆盖 R41–R47 所需的全部对象。
4. 第二波 lane 编号从 007 起：A01（两条）、A05、I02、B01、B02。

## 待 owner 决定

- `erenup/integration` → `main` 的第一个 PR 何时提（建议：D01 定稿 + U05 报告出来后）。
