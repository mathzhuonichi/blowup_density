# NEXT_SESSION.md — 当前状态与下一步

更新：2026-09-13（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状（2026-09-13 下午）

- 分支模型不变：根目录干净 `main`；`erenup/integration`（worktree `000-integration`）；lane PR 由 lead 合；**PR #15 integration → main 已交 owner**。
- integration 上已注册 **6 条合同**（`R41.threshold_arithmetic`、`I01.packet`、`I02.correction`、`I03.scaling`、`A05.gradient_l6`、`A03.bounded_representative`），`Data.lean` 63 定义，HeliCorgi 移植，D01 单元 L2 正向（020），十份 spec，台账 v2。
- **待合入队列（全部 review ACCEPT，等 CI 34750241117 结束后按序合）**：合同 lane 先——#31（026 `A03.tame_products`）、#30（027 `R42.insertion_family`）、#33（029 `I02.correction_v2`）；再 lemma 模块——#28（024 齐次数据见证）、#29（025 datum ⇒ jets，L2 全关）、#32（028 F_R 闭包，g_ε ∈ F_R）。合完 = 9 条合同。
- **本地攒着未推的 integration commit**：记账 + 三处 workflow 修复（vendor 构建缓存路径；cache restore/save 拆开、失败也保存；timeout 180 分钟）。CI 结束立刻 `git push`。
- **进行中的车道（4 条 opus）**：030-A04-spec（平方 H² continuation 适配器 spec）、031-C01-spec（能量 + H¹ 吸收 spec）、032-A02-restrict-order（A02 U4+U6 证明，无分析）、033-A02-energy-u1a（A02 U1a：`ClassicalSolutionR ⇒ UniformFiniteEnergy`）。
- 合并工具：`tmp/merge_lane.sh <lane> "<msg>"`（压成一个 commit → rebase → JSON 三方合并 `tmp/merge_json3.py` → render）；`tmp/` 不入库，丢了照 memory 里的协议重写。
- 本轮关键发现（未变）：R42 寿命子句还缺 `ClassicalSolutionR.sobolev`（非紧支 u_ε）与 R42 V2 的 `hg : MemForceR g`；I03 U7c 卡 datum 路径强可测；A01 单元 A2 = A04 的 Grönwall，只建一次。

## 下一步

1. CI 结束 → push 攒着的 commit → 按上面顺序合六个 PR（`tmp/merge_lane.sh`，合同 lane 合完跑 `make check`/`make test`/`make test-mutations`/`check_contracts.py --base-ref main`）→ 再 push 一次 → 看 CI → 更新 PR #15 正文（9 条合同）。
2. 四条在跑车道回来 → 各派一个 opus reviewer 跑 Lean → 合入 → 记 CSV。
3. 第七波候选（编号从 034 起）：D01 Bindings 漂移守卫（#28/#29/#32 合入后）；B01 合同（#32 合入后）；A02 U1b（现在 A03 `bounded_representative` 已注册，缺 ∇ 的阶移和物理导数识别）；A02 U2/U3/U5（U1a 回来后）；A01 A2 = A04 Grönwall（A04 spec 回来后）；I03 U7c；R42 V2（`hg : MemForceR g`）。
4. 每次收工更新本文件；agent 运行记 `logs/AGENT_RUNS.csv`；Attempts 放 `research/<ID>/ATTEMPTS*.md`。

## 待 owner 决定

- `erenup/integration` → `main` 的第一个 PR 何时提（建议：D01 定稿 + U05 报告出来后）。
