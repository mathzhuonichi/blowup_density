# NEXT_SESSION.md — 当前状态与下一步

更新：2026-09-13（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状（2026-09-13 深夜，第三次更新）

- 分支模型：根目录直接检出 `erenup/integration`；lane PR 由 lead 合；**PR #15 integration → main 已交 owner**。`.claude/` hooks/skills；`scripts/gates.sh [modules]`、`scripts/merge_lane.sh`；坑 `logs/LESSONS.md`；总结 `logs/PROGRESS_20260913.md`。
- **CI 被 owner 账户账单挡住（14:54Z 起）**，靠本地 `scripts/gates.sh` + 全部 `Section4` 模块显式 build（最近：50 模块、全绿）。合并流程：`tmp/merge_<PR>_then_gates.sh` 模板（squash → rebase → 记账文件取 integration → merge → pull → gates）。
- integration 上 **13 条注册合同**：R41 阈值算术、I01、I02(+v2)、I03、A05、A03×2、R42、`D01.datum_lemmas`(+v2)、**`A02.uniqueness`、`A02.maximal_partial`**。A02 的 `MaximalSolutionAPI` 20 字段中 11 已注册；剩 `exists_maximal`/`maximal_unique`/`restart*`/`insertion_lifespan_eq` 及 A01 接口。
- 已合入证明模块 50 个（A02 全部非 A01 依赖单元；A04 F1/N1/G3/Z1/D1/SL6/SL8；B01 单元 1–3、6、8；B02 单元 1、3–4；C01 U1/U2/U6 + U3 速度半边；D01 四模块 + `HalfOrder` + `Pressure`(L9(c)-partial) ）；spec：A04、C01、R43、R44。
- **在跑（5/5）**：059 B02 单元 7；060 B02 单元 8；063 B01 单元 7 拆分；056 续改（把 reviewer 证的 D2 提成模块 `A04/TimeDerivative.lean`）；062 reviewer（P2 拆分）。
- 关键路线判断（056/062 的拆分结论）：A04 G1 的核心 = A01 的 datum 层正则性（动量方程 datum 形式 SL2、datum 侧阶移 SL3、H^m 分部积分 SL5）；D2 不需要 A01（钉代表元技巧）；P2 的关键是算子值 Fourier 乘子 CLM（SL3，新基础设施）+ 单元 L3。**下一个大方向：A01 的 datum 层单元（把 `HasSmoothSobolevPath` 与动量方程 datum 形式作为 A01 产出）与 P2 的乘子 CLM。**

## 下一步

1. 回来的车道 → reviewer → 续改 → PR → 合并链 → 门禁。
2. 合同：C01 lemma 合同（U1/U2/U6 + 三线性可积性）；A04 lemma 合同（F1/N1/G3/Z1/D1/SL6/SL8/D2）；B01（1–3、6、8）、B02（1、3、4、7、8）lemma 合同——把 lemma 模块接进 `make test` 闭包。
3. 单元：A04 SL2（动量 datum 形式，钉代表元）、SL3（datum 侧阶移）、SL5；P2 SL3 乘子 CLM；C01 U4/U5/U7（有 P2 或带 `MemForceR` + `∂ₜu` jets 假设的条件版）；B01 单元 9/10；B02 单元 2/5/6/9；A01 A2b（HeliCorgi mild 续接）；R42 V2 spec。
4. 每次收工更新本文件；agent 运行记 `logs/AGENT_RUNS.csv`；坑记 `logs/LESSONS.md`；Attempts 放 `research/<ID>/ATTEMPTS*.md`。

## 待 owner 决定

- **CI 被 GitHub 账单挡住（2026-09-13 14:54Z 起）**：所有 run 立即失败，annotation 为 "The job was not started because recent account payments have failed or your spending limit needs to be increased"。owner 需在 GitHub Billing & plans 处理。此前最后一次全绿 run：34759326799（13:15–14:43Z，10 条合同 + 全部已合模块）。恢复前合并只靠本地 `scripts/gates.sh` + 显式 build 全部 `Section4` 模块。

- `erenup/integration` → `main` 的第一个 PR 何时提（建议：D01 定稿 + U05 报告出来后）。
