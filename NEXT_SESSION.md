# NEXT_SESSION.md — 当前状态与下一步

更新：2026-09-14 0122Z（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状（2026-09-14 0122Z）

- 分支模型：根目录直接检出 `erenup/integration`；lane PR 由 lead 合；**PR #15 integration → main 已交 owner**。`.claude/` hooks/skills；`scripts/gates.sh [modules]`、`scripts/merge_lane.sh`；坑 `logs/LESSONS.md`。
- **CI 无额度（owner 账单）→ 本地替代 CI**：每条合并链跑 `scripts/gates.sh` + 全部 Section4 模块编译 + `check_contracts --base-ref origin/main`；并定期整跑 CI 工作流的三步对 main（`check_contracts` / `build_changed_lean` / `test_contract_mutations --skip-build`，日志 `tmp/ci_equiv_main.log`）。最近一次 09-14 0106Z：全部通过（10205 jobs）。PLAN.md 进度表带 UTC 列。
- **CI 仍被 owner 账单挡住**；每次合并后本地 `scripts/gates.sh` + 全部 `Section4` 模块显式 build（最近：92 模块、全绿）。合并链脚本用 **`bash tmp/mkchain.sh <lane> <PR> <wave> "<PR 标题>"`** 生成（不要再 sed 上一条脚本：094/103/105/106/108 五个 squash commit 标题因此错成同一句话；PR 标题与 `Merge pull request #N` 提交是对的）。
- integration 上 **22 条注册合同**（今日新增：`R42.insertion_lifespan` #95、`B02.homogeneous_partial` #99、`A01.regularity_partial` #111、`R42.insertion_lifespan_v2` #115、`B02.homogeneous_partial_v2` #116、`D01.datum_lemmas_v3` #122 = P2）；已合入 Section4 证明模块 **100+**；2026-09-13/14 共合入 PR #72–#128（约 53 条 lane）。
- 里程碑：**P2 = eq:Rpressure 已证并注册**（117 `D01/PressureJets.lean`，120 `D01.datum_lemmas` V3）；**A04 eq:Rhigh 已组装**（121 `hpr` 经 Leray 补算子自伴 + 速度 datum 横向，128 `energyIdentityHigh` 与 spec 字段 127 token 全同）——A04 合同待开，但先做硬规矩 2 的盲写双稿（130，进行中）；**B02 V2、R42 V2 合同已注册**；**A01 起步扎实**：E1/P1/m4 已证并注册；C1b 0 阶桥（119）+ 0 阶 datum 路径连续（124）已证，C1b 真正阻塞 = D01 有限阶 datum 构造子（125：升阶步已证，剩角向搬运 M）；A3 算术核心（122）；A2b 续接（126：从先验界得全区间 mild 解，一行套 vendor；角不变性欠全局 mild 唯一性）；122 审稿改判 OpenAI 层有续接判据（`Euler/BoundedMildContinuation.lean:39`），A2b 不再是 L；123 搬 pairing 文件消除 D01→A04 反向边；SIMP 已过 D01 早期/R42/A01/A04 SL3+SL5 簇（P2 链五模块在跑 129）。
- **在跑**：125 续改（有限阶 datum：保留 reviewer 的 D-b 探针、表修正）；126 审稿（A2b 续接）；129 SIMP-D01 P2 链；130 盲写 A/B（eq:Rhigh）；chain #128（124）合并中。
- 已知未入 CI 闭包：`Section4/*` 大多不在注册合同 Tests 闭包；CI 只靠 `build_changed_lean.py`。MAINT 清单（109 之后剩）：**`A04/LaplacianPairing`+`RealPairing` 整体搬到 `Paper3/`**（115 审稿：`D01/LerayLowering` 反向 import A04，两文件不用任何 A04 声明，21 个名字零碰撞）；`PressureGauge.pressureGradient_apply` 与 `D01/MomentumSlice.pressureGradient_apply` 重复（共享 Source 级 `pressureGradient` 演算模块）；`Pressure.pressureGradient_slice_smoothSquareIntegrableJets` 已无人用且更弱（docstring 过时）；111 的 `lerayComplement_orderZeroDatum_add/_sub` 成死代码；`angular_plancherel` + 8 个 B02 helper 整簇上提到新 `Paper3/AngularPlancherel.lean`（低优先级）；108 的 `longitudinal_of_longitudinal_symm` 上提；`OrderZeroDatum`/`HalfOrder` 小副本；B02 数据链副本；074 三条交换引理与 vendor 重复；`contDiff_slice_pressure` 副本**保留，不再翻**（109 已量化）。

## 下一步

1. 回来的车道 → reviewer → 续改 → PR → `tmp/mkchain.sh` 合并链 → 门禁（lead 不手改 Lean）。链串行，一次一条。
2. 待开（按顺序）：**130 comparer**（三方比对 A/B/128 → `BLIND_RHIGH.md`）→ **A04 部分合同** `Contracts/V1/EnergyHighPartial.lean`（`Chigh`/`Chigh_pos`/`energyIdentityHigh`；重述 `HasSmoothSobolevPath`/`sobolevNormAt`/`gradientSobolevNormAt` 各配 rfl 桥，128 审稿已验；绑定经 `uniqueness_toA02`；顺手收 `gradientSobolevENorm_velocity_ne_top` 进 Continuity）；A04 G2 eq:highcontinuation（Young + ζ 正则化，`Regularized.lean` 已有设备）→ eq:criterion；D01 `D-b-transport`（`memLp_coord_smul_datum`，M）+ 对 m 归纳收掉 C1b-m-D；A2b 角不变性（需 OpenAI 圆柱方程的全局 mild 唯一性或逐窗传播）；A3-L1·k 二阶范数比较；B1（速度 jet 连续 `∀ j, Continuous (jetLp j)`）；MAINT：`componentCLM`/`orderZeroDatumCLM` 搬 D01、`isSobolevDatum_zero` 三处副本、PressureJets/PressureDrop 横向论证共享引理、108 四处重复上提；C01 能量/涡量字段（可由 `pressure_drop` 的 m=0/1 实例 + 时间正则性）；I03 U7c；R43/R44（等 A04 G2）；A02 `restart*`（等 A01 H1，`forced_uniform_restart_time` 是线索）。
3. 每次收工更新本文件；agent 运行记 `logs/AGENT_RUNS.csv`；坑记 `logs/LESSONS.md`；Attempts 放 `research/<ID>/ATTEMPTS*.md`。

## 待 owner 决定

- **CI 被 GitHub 账单挡住（2026-09-13 14:54Z 起）**：所有 run 立即失败，annotation 为 "The job was not started because recent account payments have failed or your spending limit needs to be increased"。owner 需在 GitHub Billing & plans 处理。此前最后一次全绿 run：34759326799（13:15–14:43Z，10 条合同 + 全部已合模块）。恢复前合并只靠本地 `scripts/gates.sh` + 显式 build 全部 `Section4` 模块。
- PR #15 `erenup/integration` → `main` 待 owner review（内容已远超首版：22 条合同、100+ 模块，P2 已证并注册，eq:Rhigh 已组装）。
