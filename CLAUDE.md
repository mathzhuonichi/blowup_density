# CLAUDE.md — blowup_density（用 Lean 证第 4 节）

> 每次会话自动载入。新 session 先读本文件，再读 [`NEXT_SESSION.md`](NEXT_SESSION.md)（当前状态、下一步），
> 全貌和顺序看 [`PLAN.md`](PLAN.md)。台账 = `collaboration/work_items.json`（`make tasks` 看 ready 队列）；
> 记录 = `logs/`，每次 subagent 运行记一行 `logs/AGENT_RUNS.csv`。最近更新 2026-09-13。
> 细节丢失时：派 subagent 用 grep 搜本地会话记录 `~/.claude/projects/-data-8T-ping-blowup-density/*.jsonl`，不要整文件读进主上下文。

## 目标（一句话）

用 Lean 4 把 `paper/blowup_density.tex` 的**第 4 节（全空间 R³，定理 4.1–4.7）**证出来。每个结果落成
`verification/Contracts/V1/*.lean` 的版本化合同 + `Bindings/` + `Tests/`，CI 绿，传递公理只含
`propext` / `Classical.choice` / `Quot.sound`。第 3 节（环面）deferred，不做。

## 身份与 git

- 本机 gh 登录 = `erenup`（协作者，仓库级写权限，无 admin）。owner = `mathzhuonichi`。
- 主干 `main`（2026-09-13 从 `codex/section4-blueprint` 改名，见 `logs/MAIN_BRANCH_20260913.md`）。`codex/*` 都是已合入的死分支。
- 分支保护：PR 需 1 个 review，作者不能自审，CI 必须绿。
- 一条车道 = 一个 worktree + 分支 `erenup/<TASK>-<slug>` + 一个 PR。先提 claim 小 PR
  （`python3 experiments/tasks.py claim <ID> erenup && python3 experiments/tasks.py render`），再干活。
- 冲突只会出现在 `verification/contracts.json`、`collaboration/work_items.json`、`collaboration/TASKS.md`（生成物）。
  rebase 后重跑 `tasks.py render`。
- 已有的 `Contracts/V1/*`、`Tests/*` 不改；数学变了加 V2。CI 会拒绝静默修改。
- 提交前 `make check`；Lean 改动再跑 `make test`、`make test-mutations`。PR 用模板，写任务 ID、合同版本、跑过的命令。

## Lean 环境（自包含，不碰 `~/.elan`）

- 一键：`bash scripts/lean-install.sh`（幂等；装 elan + 工具链 + Mathlib 缓存 + 跑 `lake test`）。
- 之后**每个 shell 先** `. scripts/lean-env.sh`，再用 `lake` / `lean` / `make test`。
- 工具链在 `<主仓>/.elan/`，依赖在 `verification/.lake/packages/`，都 gitignored，所有 worktree 共用。
  在 worktree 里跑同一个安装脚本会自动软链 `.lake/packages` 到主仓，不重复下载。
- 版本 `leanprover/lean4:v4.34.0-rc2`（根、`formalization/`、`verification/` 一致）。
  `vendor/HeliCorgi` 是 4.32.1 的独立包，尚未与主包混编（任务 U05）。
- 依赖链：`verification` → `../formalization` → `../vendor/NavierStokesAndEuler` → mathlib（git，锁在 lake-manifest）。
- `make test` 只编译已注册合同的闭包，秒级；不会编 340 个本地文件或 2486 个 OpenAI 文件。

## 本机资源（2026-09-13 实测）

| 项 | 值 | 结论 |
|---|---|---|
| CPU / RAM | 32 核 / 123 GB（可用约 100 GB） | 5 条车道并行绰绰有余。单模块 Lean 编译峰值约 1 GB，重 Mathlib 文件 2–4 GB |
| 磁盘 | `/data_8T` 剩 3.6 TB；本仓 11 GB（`.elan` 3 GB + Mathlib 缓存 8 GB） | worktree 软链后每条车道只多几百 MB |
| GPU | RTX 5090 32 GB | **Lean 用不上**。只有跑本地模型才有用，当前用 API 模型，闲置即可 |
| 并发线程 | 每条车道 `lake build -j 6`，5 条共 30 线程 | 不要让 5 个 lake 都默认吃满 32 核 |

## 布局（只列要知道的）

| 路径 | 是什么 |
|---|---|
| `paper/sections/04-whole-space.tex` | 目标：定理 4.1–4.7 的权威陈述。附录 A/B 是它用的局部理论和嵌入 |
| `formalization/blueprint/DEPENDENCY_GRAPH.md`、`tasks.json` | 30 节点任务 DAG（数学依赖）和每个任务的精确合同 |
| `collaboration/tasks/*.md`、`work_items.json` | 任务卡 + 台账（状态 / owner / 已注册合同） |
| `verification/` | `Contracts/V1`（稳定陈述）→ `Bindings`（指向实现）→ `Tests`（类型 + 传递公理审计） |
| `formalization/NSFormalization/{Source,Paper3,Paper1}/` | 340 个既有本地 Lean。`Paper1/` 里也有可复用的 R³ 结果，目录名不代表定义域 |
| `vendor/NavierStokesAndEuler/` | OpenAI 包。Theorem 1.1 已完整形式化（sorry 0，标准 3 公理）；`ComparatorChallenges/` 的 sorry 是刻意占位 |
| `vendor/HeliCorgi/Formal/` | R³ 无外力 mild 理论：存在、唯一、显式 lifespan、continuation、真实 PDE 语义 |
| `formalization/blueprint/EXTERNAL_REUSE.md` | 三个代码库"已有什么 / 还差什么"的索引。找声明先看这里，再派 subagent 搜源码 |
| `logs/` | 审稿、修订、审计记录。新报告放这里，文件名带日期 |
| `reference/` | 论文引用的 PDF（OpenAI 166 页、Tao 2013、Taylor、arXiv 2609.10262v1 环面版等） |
| `scripts/` | `lean-install.sh`、`lean-env.sh` |
| `tmp/` | gitignored 草稿区，日志放这里 |

## 关键路径与并发

- 关键链：D01 → A01 → A02 → A04 → R43/R44 → R41（定理 4.1）。A01 还卡 U05（HeliCorgi 工具链兼容）。
- 可并行起步、互不依赖：U05、D01、A05、I01。并发上限 5 条车道。
- 帮手模型：优先 `prover` agent（`.claude/agents/prover.md`，钉 Opus 4.8，本地未提交；**新会话启动时才加载**）。
  若 `prover` 不可用则 `general-purpose` + `model: opus`（当前解析为 Opus 5, 1M）。
  lead 自己留在关键路径上，只做拆任务、比对、归并、记账。

## 硬规矩

1. **不 over-engineer**。仓库流程已经很重，不加新流程、新检查器；产出是合同和证明。
2. **陈述保真第一**。每个合同的 Lean 陈述由 2 个只读论文、互不可见的 agent 各写一版再比对，差异写进任务卡。
   kernel 负责"证明对不对"，agent 和人负责"证的是不是论文那个定理"。
3. 不用 `sorry`，不加公理，不在合同里放占位 `Prop` 字段。`Citations/` 的 schematic axiom 和
   `Paper1/BoundaryCorollary.lean` 的 sorry 不得 import。
4. **正负例都记**。证不出的引理、试过的路径、失败原因，追加到 `collaboration/tasks/<ID>.md` 末尾的 `## Attempts` 段。
5. **报告讲人话**，固定四段：证了哪个定理 / Lean 里现在有什么 / 缺口是什么 / 跑了什么命令、什么结果。
6. 关键细节写进 md，不留在对话里。每次收工更新 `NEXT_SESSION.md`。
7. 不改 `paper/` 里的数学陈述。发现论文问题只写进 `logs/`，交 owner 决定。
8. 仓库根目录保持干净：不放松散 PDF，引用材料进 `reference/` 并在其 README 登记。

## 沟通

中文、简洁。动手前一句话说明改什么、为什么。不复述 diff。
