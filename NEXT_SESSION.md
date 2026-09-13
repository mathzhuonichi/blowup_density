# NEXT_SESSION.md — 当前状态与下一步

更新：2026-09-14 深夜（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状（2026-09-14 深夜）

- 分支模型：根目录直接检出 `erenup/integration`；lane PR 由 lead 合；**PR #15 integration → main 已交 owner**。`.claude/` hooks/skills；`scripts/gates.sh [modules]`、`scripts/merge_lane.sh`；坑 `logs/LESSONS.md`。
- **CI 仍被 owner 账单挡住**；每次合并后本地 `scripts/gates.sh` + 全部 `Section4` 模块显式 build（最近：92 模块、全绿）。合并链脚本用 **`bash tmp/mkchain.sh <lane> <PR> <wave> "<PR 标题>"`** 生成（不要再 sed 上一条脚本：094/103/105/106/108 五个 squash commit 标题因此错成同一句话；PR 标题与 `Merge pull request #N` 提交是对的）。
- integration 上 **21 条注册合同**（今日新增：`R42.insertion_lifespan` #95、`B02.homogeneous_partial` #99、`A01.regularity_partial` #111、`R42.insertion_lifespan_v2` #115、`B02.homogeneous_partial_v2` #116）；已合入 Section4 证明模块 **95+ 个**；2026-09-13/14 共合入 PR #72–#118（约 47 条 lane）。
- 里程碑：**P2 = eq:Rpressure 已证**（117 `D01/PressureJets.lean`：`∇p(t,·) ∈ H^∞`，0 阶 Leray 恒等式 + 逐阶提升；含 order-m 恒等式导出与 A04 `hP` 槽的 `∃` 形式；合同待注册为 `D01.datum_lemmas` **V3**，reviewer 已给三个字段与绑定项，见 `research/D01/REVIEW_SL8_ASSEMBLY.md` §6）；**A04 SL3、SL5 闭合**，eq:Rhigh 组装现在只欠 `hpr : ⟪G,P⟫ = 0`（`HighEnergy.lean:105`；`hP` 已由 P2 解锁；便宜路线 = `lerayComplement` 自伴 + 速度 datum 横向，树里还没有自伴引理，见 REVIEW §7）；**B02 V2 合同已注册**（`separatedAssembly@−3/2<s` + `approxCompactHomogeneous`，19/20 字段，只剩无消费者的 `annularPathApprox`）；**R42 V2 合同已注册**（`solution`/`maximal`/`blowup_limsup`）；**A01**：E1/P1/m4 已证、部分合同已注册，C1b 载体桥拆分起步中（119），脊柱 A3/B1/C1c 未开；SIMP 已过：D01 早期八模块、R42 七模块、A01 四模块、A04 SL3 簇（SL5 簇在跑）；109 上提 8 条 Paper3 级事实。
- **在跑**：115 续改（SIMP-A04 SL3：换成真负例）；118 SIMP-A04 SL5 簇；119 A01 C1b 拆分起步；chain #118（117 P2）合并中。
- 已知未入 CI 闭包：`Section4/*` 大多不在注册合同 Tests 闭包；CI 只靠 `build_changed_lean.py`。MAINT 清单（109 之后剩）：**`A04/LaplacianPairing`+`RealPairing` 整体搬到 `Paper3/`**（115 审稿：`D01/LerayLowering` 反向 import A04，两文件不用任何 A04 声明，21 个名字零碰撞）；`PressureGauge.pressureGradient_apply` 与 `D01/MomentumSlice.pressureGradient_apply` 重复（共享 Source 级 `pressureGradient` 演算模块）；`Pressure.pressureGradient_slice_smoothSquareIntegrableJets` 已无人用且更弱（docstring 过时）；111 的 `lerayComplement_orderZeroDatum_add/_sub` 成死代码；`angular_plancherel` + 8 个 B02 helper 整簇上提到新 `Paper3/AngularPlancherel.lean`（低优先级）；108 的 `longitudinal_of_longitudinal_symm` 上提；`OrderZeroDatum`/`HalfOrder` 小副本；B02 数据链副本；074 三条交换引理与 vendor 重复；`contDiff_slice_pressure` 副本**保留，不再翻**（109 已量化）。

## 下一步

1. 回来的车道 → reviewer → 续改 → PR → `tmp/mkchain.sh` 合并链 → 门禁（lead 不手改 Lean）。链串行，一次一条。
2. 待开（按顺序）：**P2 合同**（`Contracts/V3/DatumLemmas.lean`，三字段 + `Bindings.DatumLemmasV3`（import `Bindings.Uniqueness` 做结构转换）+ Tests，照 REVIEW_SL8_ASSEMBLY §6/附录 C）；**A04 `hpr`**（S–M：`lerayComplement` 自伴 + `(I−P)ₘ G = 0`（速度无散，0 阶横向 + lowering）+ 117 的 `pin_pressureGradient_datum` ⇒ `⟪G,P⟫=0`，然后 `energyIdentityHigh` 组装）；MAINT 搬 pairing 到 Paper3（等 115 合入）；A01 m2 `pressure_recovery`（仍缺 t=0 端点 + 逐点散度，P2 不直接解锁）；C01 能量/涡量字段；I03 U7c；`RegularityPartial` V2 时把 `pressure_potential_of_pointwise` 的冗余 `hsym` 去掉（113 审稿证明可推出）；A01 L 单元拆分（A2/A2b、A3、B1、C1c）；R43/R44（等 A04 组装）；A02 `restart*`（等 A01 H1）。
3. 每次收工更新本文件；agent 运行记 `logs/AGENT_RUNS.csv`；坑记 `logs/LESSONS.md`；Attempts 放 `research/<ID>/ATTEMPTS*.md`。

## 待 owner 决定

- **CI 被 GitHub 账单挡住（2026-09-13 14:54Z 起）**：所有 run 立即失败，annotation 为 "The job was not started because recent account payments have failed or your spending limit needs to be increased"。owner 需在 GitHub Billing & plans 处理。此前最后一次全绿 run：34759326799（13:15–14:43Z，10 条合同 + 全部已合模块）。恢复前合并只靠本地 `scripts/gates.sh` + 显式 build 全部 `Section4` 模块。
- PR #15 `erenup/integration` → `main` 待 owner review（内容已远超首版：21 条合同、95+ 模块，P2 已证）。
