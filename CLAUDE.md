# CLAUDE.md — blowup_density（当前：Phase 5，关闭 6 个 Partial）

> 新 session 先读 [NEXT_SESSION.md](NEXT_SESSION.md)，再读 [PLAN.md](PLAN.md)（Partial 评估表、lane 进度表）。
> owner 的现状与检查见 `README.md`、`formalization/blueprint/`、`output/pdf/formalization_guide.pdf`（2026-09-21 精简提交 `1a1b53b6`）。
> 第 3/4 节已完成并合入 `main`（PR #259、#270）；历史文档见 `archive/section3/`、`archive/section4/`。不把旧快照的未完成项当作新工作。
> 记录 = `logs/`；lane 简报 `collaboration/briefs/`；研究记录 `research/<节点>/`。

## 目标（一句话）

在 owner 的新 `main` 上关闭文章级的 6 个 Partial（Thm 3.6 任意球、Lemma 3.5 文章形式、Remark 3.13、Prop 3.16/3.17 有界域、Prop 2.1 H¹ restart 先评估），每个都落成 V2 合同 + 蓝图/guide 更新。
结果落成版本化合同、绑定与测试；传递公理只含 `propext` / `Classical.choice` / `Quot.sound`。
owner 的规则：Closed 不得依赖 Partial（`make check` 强制）；"not in Mathlib" 的初等恒等式先走零延拓/紧支撑路线再说残差（`logs/LESSONS.md` 顶部）。

## 身份与 git

- 本机 gh 登录 = `erenup`（协作者，仓库级写权限，无 admin）。owner = `mathzhuonichi`。
- 主干 `main`（2026-09-13 从 `codex/section4-blueprint` 改名，见 `logs/MAIN_BRANCH_20260913.md`）。`codex/*` 都是已合入的死分支。
- 分支保护：PR 需 1 个 review，作者不能自审，CI 必须绿。
- **2026-09-20 起核心分支 `erenup/core`**（根目录即它）= `origin/main` + 流程层。lane 从它开 worktree、PR 以它为 base、lead 在根目录合入；`scripts/*.sh` 默认 `INTEGRATION_BRANCH=erenup/core`。老 `erenup/integration`、`erenup/integration-section3` 冻结。交付：从 `main` 切 `erenup/delivery-<n>`，只带 `formalization/ verification/ paper/ experiments/` 差异，唯一 PR 给 `main`。
- **编号规则**：lane 序号 `NNN` 三位、全局递增，唯一分配点是 `PLAN.md` 进度表。
  worktree = `.claude/worktrees/NNN-<TaskID>-<slug>`，分支 = `erenup/NNN-<TaskID>-<slug>`，PR 标题 = `[NNN-<TaskID>] 一句话`。
  TaskID 用当前 DAG 节点（T10–T24；历史 D01…R47）；非节点的工程活用 `MAINT`，纯陈述整理用 `SPEC`。（`000-integration` worktree 已退役，根目录即集成分支。）
- 一条 lane：从 `erenup/core` 开 worktree（`LEAN_SEED_DIR=<根或最近 worktree> bash scripts/lean-install.sh`）→ 简报 `tmp/codex/briefs/<lane>.md`（复制到 `collaboration/briefs/`）→ `tmp/launch_when_free.sh <lane> <m1> <m2> <brief>` → 干活（草稿放 `research/<ID>/`）→ `tmp/retry_review.sh` codex 审稿 → PR to `erenup/core` → lead 合入并记 `PLAN.md` 行 + `logs/AGENT_RUNS.csv`。owner 删了 `tasks.py`/`work_items.json`，不再 claim/render。
- 冲突只会出现在 `verification/contracts.json`（`tmp/json_merge_contracts.py`）、`formalization/blueprint/*.json`、`logs/AGENT_RUNS.csv`、`PLAN.md`（`tmp/union_merge.py` 只并 md/csv）。CSV 只由 lead 在合入时追加。
- 已有的 `Contracts/V1/*`、`Tests/*` 不改；数学变了加 V2。CI 会拒绝静默修改。
- **合同 import 规则**（`check_contracts.py` 强制）：`Contracts/*` 只能 import `Mathlib` / `Lean` / `Init` / `Contracts.*`。
  上游或本地的定义要在合同里逐字重写，绑定层用 `rfl` 桥定理（`theorem foo_eq : Contract.foo = Upstream.foo := rfl`）防漂移；每个重写的定义都要有桥。
  **结构体例外**：`ClassicalSolutionR` 这类 `structure` 只在 `Contracts/V1/Data.lean` 里定义，`formalization/` 不能 import 它，本地重述出来的是另一个归纳类型，`rfl` 桥不可能；绑定层用逐字段的双向转换函数（字段类型 defeq）+ 往返引理。本地重述只允许一份（`Section4/A02/Restrict.lean` §0 是当前那份；后续模块 import 它，不再抄）。
  **临时放宽（integration 分支，待 owner 批准）**：009 把规则放宽为"+ 上游 `NavierStokes.*` + 6 个本地规范定义模块白名单"（见 `check_contracts.py` 的 `CONTRACT_CANONICAL_MODULES`）。扩白名单是政策变更，不是日常改动。
- `verification/Tests` 是 `warningAsError = true`：任何 Tests 模块都不能 import HeliCorgi 的 `Formal.*`（52 个上游 warning 会变成 error），先经过 Bindings。
- 提交前 `make check`（owner 的：蓝图一致性 + 注册表 + 政策测试）；Lean 改动再跑 `make test`、`make test-mutations`；关闭 Partial 还要 `python3 experiments/check_formalization_plan.py`（重生成 DEPENDENCY_GRAPH）、`audit_article_axioms.py --build --output-dir …`、`make paper`。PR 写任务 ID、合同版本、跑过的命令。
- **hooks / skills**（`.claude/`，会话启动时加载）：`hooks/guard.py` 拦四种已经付过学费的错误（在 `formalization/` 下跑 lake、直接 push main、裸 `git stash`、手改生成的任务卡 / `paper/` / 冻结的 `Contracts/V1`、`Tests`）；`hooks/post_lean.py` 每次改 `.lean` 后查 `sorry/admit/axiom/native_decide` 并对合同文件跑 import 政策。`/lane-merge`、`/lane-review` 是合入与审稿的固定流程。新建 lane 的 `lean-install.sh` 会从 `000-integration` 复制编译产物，首次 `lake` 从约一小时降到分钟级。
- **CI 是 `cancel-in-progress`**：integration → main 的 PR 在跑 CI 时（约 20 分钟），不要往 integration 连续 push 小 commit，会把 run 取消。记录类 commit 攒着，CI 结束再 push。用 `gh run list --branch erenup/integration` 看状态（`gh pr checks` 对这个 workflow 不显示）。

## Lean 环境（自包含，不碰 `~/.elan`）

- 一键：`bash scripts/lean-install.sh`（幂等；装 elan + 工具链 + Mathlib 缓存 + 跑 `lake test`）。
- 之后**每个 shell 先** `. scripts/lean-env.sh`，再用 `lake` / `lean` / `make test`。
- 工具链在 `<主仓>/.elan/`，依赖在 `verification/.lake/packages/`，都 gitignored，所有 worktree 共用。
  在 worktree 里跑同一个安装脚本会自动软链 `.lake/packages` 到主仓，不重复下载。
- 版本 `leanprover/lean4:v4.34.0-rc2`（根、`formalization/`、`verification/` 一致）。
  `vendor/HeliCorgi` 源码是 4.32.1，但 U05 已把它在本 pin 下**就地编进主 workspace**：`formalization/lakefile.toml` 的 `Formal` 库（`srcDir` 指向 vendor，88 个显式 root，vendor 零改动）＋ `FormalPatched` 库（4 个在 4.34.0-rc2 下编不过的模块的补丁副本）。`Formal.MildSolutionSemantics` / `MildFlowMapBridge` / `MildZeroUniqueness` 不在 root 列表，`lake build` 报 `unknown target`，要用先加 root（配置变更）。
- 依赖链：`verification` → `../formalization` → `../vendor/NavierStokesAndEuler` → mathlib（git，锁在 lake-manifest）。
- `make test` 只编译已注册合同的闭包，秒级；不会编 340 个本地文件或 2486 个 OpenAI 文件。
- 草稿文件放 `research/<ID>/X.lean`，检查用 `cd verification && lake env lean ../research/<ID>/X.lean`；
  它 import 的本地模块先 `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Foo.Bar`（首次一个闭包约 2–3 分钟，之后秒级）。
  **lake 永远从 `verification/` 跑**（`formalization/` 是它的依赖，从那里跑 lake 会把 `formalization/` 当独立 workspace、重新 clone 一份 Mathlib；只有 `verification/.lake/packages` 被软链）。

## 本机资源（2026-09-13 实测）

| 项 | 值 | 结论 |
|---|---|---|
| CPU / RAM | 32 核 / 123 GB（可用约 100 GB） | 5 条车道并行绰绰有余。单模块 Lean 编译峰值约 1 GB，重 Mathlib 文件 2–4 GB |
| 磁盘 | `/data_8T` 剩 3.6 TB；本仓 11 GB（`.elan` 3 GB + Mathlib 缓存 8 GB） | worktree 软链后每条车道只多几百 MB |
| GPU | RTX 5090 32 GB | **Lean 用不上**。只有跑本地模型才有用，当前用 API 模型，闲置即可 |
| 并发线程 | 每条车道 `LEAN_NUM_THREADS=6`（此版 Lake 没有 `-j`），5 条共 30 线程 | 不要让 5 个 lake 都默认吃满 32 核 |

## 布局（只列要知道的）

| 路径 | 是什么 |
|---|---|
| `paper/sections/03-torus.tex`、`collaboration/SECTION3_PLAN.md` | 当前目标：第 3 节；T10–T24 DAG 与表示层决策 |
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

- 当前：P1–P5 并行（492–495、496–498），P6 只评估（499）；先 491 确认新 main 可编译。见 `PLAN.md` §1–§2。
- 并发与模型按 lane 简报及用户指示执行；当前不从历史未完成清单自动开 lane。
- **帮手模型（用户 2026-09-19 规矩）：不启动 Opus 子代理**；全部 codex 在 tmux（gpt-6-astra low = 硬分析/装配/规划；gpt-5.6-sol xhigh = 簿记/注册/审稿）。lead 自己只做拆任务、比对、归并、记账，不跑全量编译、不改代码（记录/注释/空白类微改除外）。

## 硬规矩

1. **不 over-engineer**。仓库流程已经很重，不加新流程、新检查器；产出是合同和证明。
2. **陈述保真第一**。每个合同的 Lean 陈述由 2 个只读论文、互不可见的 agent 各写一版再比对，差异写进任务卡。
   kernel 负责"证明对不对"，agent 和人负责"证的是不是论文那个定理"。
3. 不用 `sorry`，不加公理，不在合同里放占位 `Prop` 字段。`Citations/` 的 schematic axiom 和
   `Paper1/BoundaryCorollary.lean` 的 sorry 不得 import。
4. **正负例都记**。证不出的引理、试过的路径、失败原因，写到 `research/<ID>/ATTEMPTS.md`（非生成文件）；跨任务的坑和经验一行一条加到 `logs/LESSONS.md` 顶部。
   每个合入的证明模块随后过一遍 simplifier + tester（见 `/lane-review` 末段），再进合同。
   `collaboration/tasks/*.md` 和 `TASKS.md` 是 `tasks.py render` 生成的，**手写内容会被下次 render 整文件覆盖**，不要往里追加。
5. **报告讲人话**，固定四段：证了哪个定理 / Lean 里现在有什么 / 缺口是什么 / 跑了什么命令、什么结果。
6. 关键细节写进 md，不留在对话里。每次收工更新 `NEXT_SESSION.md`。
7. 不改 `paper/` 里的数学陈述。发现论文问题只写进 `logs/`，交 owner 决定。
8. 仓库根目录保持干净：不放松散 PDF，引用材料进 `reference/` 并在其 README 登记。

## 沟通

中文、简洁。动手前一句话说明改什么、为什么。不复述 diff。
