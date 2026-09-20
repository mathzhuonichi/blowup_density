# 第 4 节交付物完整编译验证（2026-09-17）

独立验证：冻结分支 `erenup/integration`（PR #259 → `main`）上的第 4 节交付物能否从零完整编译，
三道门禁是否通过，37 个已注册合同的传递公理是否干净。
验证在专用 worktree `.claude/worktrees/S4-full-build`（分支 `erenup/S4-full-build`）中进行，
**未修改任何 Lean 文件、合同、测试或台账**，只新增本报告。

## 1. 环境（Environment）

| 项 | 值 |
|---|---|
| 被验证 commit | `ee71af7db3b59609917048e55c3120c0ed906692`（`origin/erenup/integration`，2026-09-16 15:13:30 -0400，"T13 reconciliation (lead); 265 draft A done"） |
| 与 PR #259 一致性 | `gh pr view 259` 的 `headRefOid` = `ee71af7d…` ✓ 同一 commit |
| 工具链 | `leanprover/lean4:v4.34.0-rc2`（根 / `formalization/` / `verification/` 三处 `lean-toolchain` 一致） |
| Lean | 4.34.0-rc2, x86_64-unknown-linux-gnu, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Lake | 5.0.0-src+6a10ac8 |
| Mathlib | rev `85e3a25e006c`（inputRev `v4.34.0-rc2`，锁在 `verification/lake-manifest.json`） |
| 验证日期 | 2026-09-17（UTC） |
| 机器 | 32 核 / 123 GB，验证期间 load ≈ 0.6（空闲） |

安装：`LEAN_SEED_DIR=/data_8T/ping/blowup_density bash scripts/lean-install.sh`，**7 秒完成**
（从主仓 seed 复制 `formalization/`、`vendor/NavierStokesAndEuler/`、`verification/` 三处 `.lake/build`；
`verification/.lake/packages` 软链主仓）。日志显示 `Using cache from origin: (some leanprover-community/mathlib4)`，
**没有从源码 clone 或重编 Mathlib**。日志：`tmp/s4_install.log`。

## 2. 完整编译（Full build）

### 2.1 模块数是 206，不是 205

任务书给的列举命令 `git ls-files 'formalization/NSFormalization/Section4/**/*.lean'` 返回 **205**，
但它漏掉了直接位于 `Section4/` 下、不在任何子目录里的 `Section4/HeliCorgiPort.lean`
（git pathspec 的 `**/` 在此不匹配零层目录）。改用 `git ls-files 'formalization/NSFormalization/Section4/'`
得到 **206** 个 `.lean`，与磁盘上 `find` 的 206 个一致。本次验证编译的是全部 **206** 个模块。

### 2.2 先做了一次真正的重编译，而不是缓存回放

第一次 `lake build`（206 个目标）**3 秒**就返回 `Build completed successfully`——因为 seed 过来的
`.lake/build` 已经包含全部第 4 节产物，lake 只做了 trace 校验和回放。这只能证明"产物与源码的哈希对得上"，
不能证明"现在这套工具链能把它编出来"。因此删除了
`formalization/.lake/build/{lib/lean,ir}/NSFormalization/Section4`（清空后该路径下 0 个文件），
强制 206 个模块全部重新 elaborate，Mathlib 与其余依赖保持缓存。

> 附带发现：seed 过来的 build 目录里有 2 个**陈旧 olean**，源码已不存在——
> `NSFormalization/Section4/A04/LaplacianPairing.olean`、`A04/RealPairing.olean`。
> 它们是历史删除文件的残留，不属于交付物，已随本次清理消失，不影响任何结论。

### 2.3 结果

```
START 1789678548  Thu Sep 17 08:55:48 PM UTC 2026
END   1789678780  Thu Sep 17 08:59:40 PM UTC 2026
LAKE_EXIT=0
```

| 指标 | 值 |
|---|---|
| 编译模块数 | **206 / 206**（日志中 `Built NSFormalization.Section4.*` 恰好 206 行） |
| 墙钟时间 | **232 秒（3 分 52 秒）**，`LEAN_NUM_THREADS=6`，单次 `lake build` 调用 |
| lake 退出码 | **0** |
| lake 末行 | **`Build completed successfully (10636 jobs).`** |
| **错误数** | **0**（`grep -cE "^error\|error:"` = 0） |
| 最慢模块 | `A01.DatumPathSmooth` 15s、`A03.ScalarTameProduct` 11s、`A01.AprioriFamily` 11s |

日志：`tmp/s4_full_build.log`、`tmp/s4_build_times.txt`。

### 2.4 警告（是 warning，不是 error）

日志中含 `warning:` 的行共 95 行，其中 21 行是多行警告的 `Hint:` 续行，**实际警告 74 条**：

| 来源 | 条数 | 性质 |
|---|---|---|
| 依赖 `vendor/HeliCorgi/Formal/*` | 46 | 上游既有 linter 警告，依赖回放时带出 |
| 依赖 `NSFormalization/{Source,Paper3}/*` | 26 | 本地既有模块的 linter 警告，非第 4 节代码 |
| **第 4 节自身源码** | **2** | 见下 |

第 4 节自身只有 2 条，且都是同一条无害的风格 linter：

```
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.
```

全部 74 条都是 warning，没有一条是 error；`verification/Tests` 的 `warningAsError = true` 只作用于
`Tests.*`，这些警告不在其中，`make test` 仍然通过。

## 3. 三道门禁（Gates）

全部在 worktree 根目录执行，退出码均为 **0**。

### `make check` → exit 0（约 10 秒），日志 `tmp/s4_gate_check.log`

```
python3 experiments/check_formalization_plan.py --check
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
python3 experiments/test_contract_policy.py
.............
Ran 13 tests in 0.046s
OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### `LEAN_NUM_THREADS=6 make test` → exit 0（26 秒），日志 `tmp/s4_gate_test.log`

末行：

```
ℹ [10732/10732] Built Tests.CompletedDensity (2.7s)
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
```

错误数 0。

### `LEAN_NUM_THREADS=6 make test-mutations` → exit 0（12 秒），日志 `tmp/s4_gate_mutations.log`

```
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

### `python3 experiments/check_contracts.py --base-ref main`

日志 `tmp/s4_check_contracts.log`：

- `registered_contracts` = **37**
- `base_compatibility_checked` = **true**

（`make check` 内部那次不带 `--base-ref`，因此同一字段为 `false`，属预期。）

## 4. 合同公理审计（Contract axiom audit）

`make test` 对每个已注册合同跑 `TestSupport.checkAxioms`，该检查只允许
`propext` / `Classical.choice` / `Quot.sound`，出现其他公理即 `throwError`。

测试日志中 `... checked; standard logical axioms only` 共 **39 行、39 个互不重复的声明**：
其中 **37 个正是 `verification/contracts.json` 里 37 条合同登记的 `declaration`**，
经程序比对 **没有任何已注册合同缺席**（registry 声明集合 ⊆ 已审计集合，差集为空）。

另外 2 个是登记表之外、顺带被审计的声明（额外保障，不是遗漏）：

- `BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4`（V3 ← V4 的绑定桥引理）
- `BlowupDensity.Tests.energyAbsorptionV4_terminalFinite`（V4 的派生事实）

37 条合同（id / 版本 / 被审计声明）：

| # | 合同 id | 版本 | 声明 |
|---|---|---|---|
| 1 | A01.local_theory_v2 | v2 | `Tests.checkedLocalTheoryV2` |
| 2 | A01.regularity_partial | v1 | `Tests.checkedRegularityPartial` |
| 3 | A02.maximal_partial | v1 | `Tests.checkedMaximalPartial` |
| 4 | A02.maximal_partial_v2 | v2 | `Tests.checkedMaximalPartialV2` |
| 5 | A02.uniqueness | v1 | `Tests.checkedUniqueness` |
| 6 | A03.bounded_representative | v1 | `Tests.checkedBoundedRepresentative` |
| 7 | A03.tame_products | v1 | `Tests.checkedTameProduct` |
| 8 | A04.continuation_v2 | v2 | `Tests.checkedContinuationV2` |
| 9 | A04.energy_high_partial | v1 | `Tests.checkedEnergyHighPartial` |
| 10 | A04.energy_high_partial_v2 | v2 | `Tests.checkedEnergyHighPartialV2` |
| 11 | A05.gradient_l6 | v1 | `Tests.checkedGradientL6` |
| 12 | A05.gradient_l6_v2 | v2 | `Tests.checkedGradientL6V2` |
| 13 | B01.bochner_partial | v1 | `Tests.checkedBochnerPartial` |
| 14 | B02.homogeneous_partial | v1 | `Tests.checkedHomogeneousPartial` |
| 15 | B02.homogeneous_partial_v2 | v2 | `Tests.checkedHomogeneousPartialV2` |
| 16 | C01.energy_absorption_partial | v1 | `Tests.checkedEnergyAbsorptionPartial` |
| 17 | C01.energy_absorption_partial_v2 | v2 | `Tests.checkedEnergyAbsorptionPartialV2` |
| 18 | C01.energy_absorption_partial_v3 | v3 | `Tests.checkedEnergyAbsorptionPartialV3` |
| 19 | C01.energy_absorption_v4 | v4 | `Tests.checkedEnergyAbsorptionV4` |
| 20 | D01.datum_lemmas | v1 | `Tests.checkedDatumLemmas` |
| 21 | D01.datum_lemmas_v2 | v2 | `Tests.checkedDatumLemmasV2` |
| 22 | D01.datum_lemmas_v3 | v3 | `Tests.checkedDatumLemmasV3` |
| 23 | D01.homogeneous_norm | v1 | `Tests.checkedHomogeneousNorm` |
| 24 | I01.packet | v1 | `Tests.checkedPacket` |
| 25 | I02.correction | v1 | `Tests.checkedCorrection` |
| 26 | I02.correction_v2 | v2 | `Tests.checkedCorrectionV2` |
| 27 | I03.scaling | v1 | `Tests.checkedScaling` |
| 28 | R41.main_thresholds | v1 | `Tests.checkedMainThresholds` |
| 29 | R41.threshold_arithmetic | v1 | `Tests.checkedThresholds` |
| 30 | R42.insertion_family | v1 | `Tests.checkedInsertionFamily` |
| 31 | R42.insertion_lifespan | v1 | `Tests.checkedInsertionLifespan` |
| 32 | R42.insertion_lifespan_v2 | v2 | `Tests.checkedInsertionLifespanV2` |
| 33 | R43.critical_regularity | v1 | `Tests.checkedCriticalRegularity` |
| 34 | R44.critical_finite_horizon | v1 | `Tests.checkedCriticalFiniteHorizon` |
| 35 | R45.force_classes | v1 | `Tests.checkedForceClasses` |
| 36 | R46.completed_density | v1 | `Tests.checkedCompletedDensity` |
| 37 | R47.grid_observations | v1 | `Tests.checkedGridObservations` |

**没有任何合同缺席审计。**（明细：`tmp/s4_contract_audit.txt`）

## 5. 禁用记号扫描（Forbidden-token scan）

`grep -rnE "\bsorry\b|\badmit\b|^axiom |native_decide" formalization/NSFormalization/Section4/`
共 20 处命中，**逐条核对后全部是模块文档注释里的散文**，没有一处是真实的证明占位或公理声明：

- 17 处形如 `` No `sorry`, no `axiom`; `#print axioms` is standard (...) ``（D01/A01/A04 各模块的文档段）
- 1 处 `A04/LaplacianDatum.lean:32` `` ## What remains (the SL3 gap, unproved here, no `sorry`) ``
- 2 处 `R43/Pieces.lean:14-15` `` It contains no `sorry`, no `axiom`, no `native_decide`, and no placeholder `Prop`. ``

分项复核：

| 检查 | 结果 |
|---|---|
| 行首 `axiom ` 声明 | **0** |
| `native_decide` | 仅 `R43/Pieces.lean:15` 一处，且在散文中 |
| 去掉反引号/散文后的 `sorry` / `admit` 真实用法 | **0** |
| 编译日志中的 `declaration uses 'sorry'` | **0**（206 个模块全部 elaborate，无此警告） |

即：第 4 节 206 个模块**无 `sorry`、无 `admit`、无自定义 `axiom`、无 `native_decide`**。

### 心跳上限（maxHeartbeats）

`Section4/` 下共 48 处 `set_option maxHeartbeats`，其中 **5 处超过 400000**：

```
NSFormalization/Section4/A03/ScalarTameProduct.lean:249:   set_option maxHeartbeats 1200000 in
NSFormalization/Section4/A01/ForcedSourceUpgrade.lean:51:  set_option maxHeartbeats 800000 in
NSFormalization/Section4/A01/ForcedSourceUpgrade.lean:85:  set_option maxHeartbeats 800000 in
NSFormalization/Section4/A01/ForcedMaximalRegularity.lean:58: set_option maxHeartbeats 800000 in
NSFormalization/Section4/A01/ContinuationInvariant.lean:60: set_option maxHeartbeats 600000 in
```

这 5 处只是放宽 elaborate 预算，不影响可靠性（kernel 仍完整检查）；对应模块的实测编译时间
分别为 11s / 10s / 10s / 6s 量级，远未接近超时，说明预算留有余量。

## 6. 结论（Verdict）

**commit `ee71af7d` 上第 4 节的全部 206 个 Lean 模块在 v4.34.0-rc2 + Mathlib `85e3a25e` 下
从清空产物起 232 秒内零错误完整重编译（`Build completed successfully (10636 jobs)`），
`make check` / `make test` / `make test-mutations` 三道门禁全部通过，
37 个已注册合同无一缺席公理审计且只依赖 `propext` / `Classical.choice` / `Quot.sound`，
源码无 `sorry` / `admit` / 自定义 `axiom` / `native_decide`——PR #259 的交付物编译与审计状态干净、可合入。**

## 附：本次跑过的命令与日志

| 命令 | 日志 | 结果 |
|---|---|---|
| `LEAN_SEED_DIR=… bash scripts/lean-install.sh` | `tmp/s4_install.log` | exit 0，7s，未重编 Mathlib |
| `cd verification && LEAN_NUM_THREADS=6 lake build <206 modules>` | `tmp/s4_full_build.log`、`tmp/s4_build_times.txt` | exit 0，232s，0 error |
| `make check` | `tmp/s4_gate_check.log` | exit 0 |
| `LEAN_NUM_THREADS=6 make test` | `tmp/s4_gate_test.log` | exit 0，39 条公理审计 |
| `LEAN_NUM_THREADS=6 make test-mutations` | `tmp/s4_gate_mutations.log` | exit 0，4 个变异用例符合预期 |
| `python3 experiments/check_contracts.py --base-ref main` | `tmp/s4_check_contracts.log` | 37 合同，base 兼容已校验 |
| 禁用记号 / 心跳扫描 | `tmp/s4_heartbeats.txt`、`tmp/s4_contract_audit.txt` | 见 §4–§5 |

（`tmp/` 是 gitignored 草稿区，路径相对于主仓 `/data_8T/ping/blowup_density`。）
