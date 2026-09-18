# Section 3 集成分支全量编译检查（2026-09-18）

目的：今晚约 25 次合入之后，验证 `erenup/integration-section3` 上 Section 3 的**全部**模块
在同一份源码树里能一起编译通过（语义合并冲突：两条分支各自 clean merge、放一起编不过）。
只读检查，不修任何 tracked 文件。

## 环境

| 项 | 值 |
|---|---|
| 被检提交 | `2488ed4149c6f32b48b8b09ee76141e83f9f8ab7`（`origin/erenup/integration-section3`，"338 done (Opus): H3 existence input proved…"） |
| worktree | `.claude/worktrees/S3-full-build-2`（分支 `erenup/S3-full-build-2`，从 origin 新开，未 push） |
| 安装 | `LEAN_SEED_DIR=/data_8T/ping/blowup_density bash scripts/lean-install.sh`（软链主仓 `.lake/packages` + 复制编译产物），`== OK` |
| 工具链 | `Lean (version 4.34.0-rc2, commit 6a10ac8c22be, Release)`；根 / `verification/` 的 `lean-toolchain` 一致 |
| 机器 | 32 核 / 123 GB（可用约 101 GB）；`LEAN_NUM_THREADS=6` |
| 运行方式 | `. scripts/lean-env.sh`，`lake` 一律从 `verification/` 跑 |

## Section 3 模块数与全量编译

`find formalization/NSFormalization/Section3 -name '*.lean'` = **35 个模块**：

| 目录 | 模块数 |
|---|---|
| `Section3/T10/` | 7（DatumBasics, ForcePaths, FourierCalculus, Leray, Parseval, PeriodicData, PhysicalBridge） |
| `Section3/T11/` | 25（ClassicalAssembly, ConvolutionBound, ConvolutionBoundReal, CriterionBridge, DuhamelHalfStep, EnergyIdentity, ExtendsBeyond, FlowConversion, FractionalSmoothing, GalileanClasses, HighOrder, LocalExistence, LocalExistenceProbe, LocalTheory, Maximal, MeanIdentity, MildMomentum, MildPressure, Persistence, PhysicalRecovery, Rescaling, Restart, RestartBeyond, Transport, Uniqueness） |
| `Section3/T12/` | 2（MeanZeroCalculus, SpectralGap） |
| `Section3/T13/` | 1（Localization） |

先删掉且只删掉 Section 3 的编译产物
（`formalization/.lake/build/lib/lean/NSFormalization/Section3/`、`…/ir/NSFormalization/Section3/`，
删前仅 T10 的 5 个模块有产物，T11/T12/T13 本来就是从零编），再跑**一条**命令：

```
cd verification && LEAN_NUM_THREADS=6 lake build <35 个模块名>
```

结果：

| 项 | 值 |
|---|---|
| 退出码 | **0** |
| 墙上时间 | **89 s** |
| error | **0** |
| Section 3 模块 Built | **35 / 35**（Replayed 0，即全部真正重编） |
| 顺带新编的非 Section 3 模块 | 54（Paper1 41、Source 8、Paper3 5——都是 Section 3 lane 依赖的既有本地模块） |
| Replayed（缓存回放）目标 | 26 |
| warning 行 | 96，**Section 3 源文件贡献 0 行** |
| `.olean` 落盘 | 35 / 35 |

**warning 分类**：96 行 warning 全部来自非 Section 3 的既有 / 上游模块，
按文件计 24 个：`NSFormalization/Paper1/*`（PeriodicLocalLifespan 5、PeriodicCorrectionEndpointRates 4、
PeriodicH2Embedding 3 等）、`NSFormalization/Source/*`（RealSobolev、FiniteHilbertBochner、
BoundedReference* 等）、`NSFormalization/Paper3/*`、`NSFormalization/Section4/A01/*`
（AprioriFamily、MildGronwall，回放）、以及 vendor 的 `Formal.*`（R3Leray*、R3Stokes* 等，回放）。
按 linter 计：`unusedVariables` 24、`unnecessarySeqFocus` 16、`unusedSimpArgs` 7、
`unnecessarySimpa` 7、`style` 6、`unusedTactic` / `unreachableTactic` / `defProp` 各 1。
`grep 'warning: NSFormalization/Section3/'` = **0**，即 Section 3 自己的 35 个模块零 warning。

另：`grep sorry formalization/NSFormalization/Section3/*/*.lean` = **0**。

## 闸门

worktree 根目录执行：

| 命令 | 退出码 | 结果 |
|---|---|---|
| `make check` | 0 | `check_formalization_plan --check` / `check_contracts` / `test_contract_policy`（13 tests OK）/ `check_work_queue`（45 work items 一致） |
| `make test` | 0 | 2 s；40 个合同全部 `checked; standard logical axioms only` |
| `make test-mutations` | 0 | 13 s；`implementation_refactor: accepted`，`admitted_proof` / `extra_axiom` / `weakened_hypothesis` 三项均 `rejected as required` |
| `python3 experiments/check_contracts.py --base-ref main` | 0 | `registered_contracts: 38`，`base_compatibility_checked: true` |

注：`make check` 里不带 `--base-ref` 的那次报 `base_compatibility_checked: false`（预期，它没有 base）；
单独带 `--base-ref main` 跑出来是 `true`，无兼容性告警。

## Probe 与公理审计扫描

`find research/T1* \( -name '*_closes.lean' -o -name 'axioms_*.lean' \)` = **58 个文件**
（T10 11、T11 45、T12 2；T13 只有 `research/T13/probes/api_on_canonical.lean`，不匹配这两个模式，未纳入）。
逐个 `cd verification && lake env lean ../<file>`（4 路并行，`LEAN_NUM_THREADS=2`）：

| 项 | 值 |
|---|---|
| 通过 | **58 / 58** |
| 失败 / stale probe | **0** |
| 输出里的 error | 0 |
| `#print axioms` 结果 | 87 条，全部是 `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`、无自定义公理 |

## 结论

1. **没有发现语义合并冲突。** 今晚合入后的 `erenup/integration-section3`（`2488ed41`）上，
   Section 3 的 35 个模块在同一份源码树里一次性从零编译通过，0 error、0 Section 3 warning，
   35 个模块全部真正重编（无缓存回放掩盖）。
2. 四个闸门（`make check` / `make test` / `make test-mutations` / `check_contracts --base-ref main`）全绿；
   38 个注册合同、`base_compatibility_checked: true`；40 个 Tests 合同的传递公理只含标准三条。
3. 58 个 T1x probe / 公理审计文件全部通过，没有 stale probe——说明各 lane 写 probe 时的 lane base
   与当前集成分支在这些陈述上仍然对得上。
4. 96 行 warning 全是既有 / 上游模块的 linter 风格提示（Paper1/Paper3/Source/Section4/A01 与 vendor `Formal.*`），
   与今晚的合入无关，不构成回归；不在本次范围内处理。
5. 全量编译只用 89 s，说明后续每次合入后再跑一遍这个全量检查是廉价的，建议作为合入批次的收尾动作。

跑过的命令：`scripts/lean-install.sh`（安装）、`lake build`（35 模块，89 s，rc=0）、
`make check`、`make test`、`make test-mutations`、`check_contracts.py --base-ref main`、
`lake env lean` × 58。
