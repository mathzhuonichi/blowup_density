# Section 3 集成分支全量编译检查（2026-09-18）

目的：验证当前集成批次（#339–#353 合入后）Section 3 全部模块可在同一源码树编译；只读检查。

## 环境

| 项 | 值 |
|---|---|
| 被检提交 | `dbdac830cec09b6cd3d2aa81823e67a0051ddb70` |
| worktree | `.claude/worktrees/399-MAINT-section3-build-e` |
| 工具链 | Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release) |
| 线程 | `LEAN_NUM_THREADS=6` |
| 运行方式 | `. scripts/lean-env.sh`；`lake` 从 `verification/` 执行（`make test` 使用 `lake -d verification test`） |

## Section 3 模块数与全量编译

`find formalization/NSFormalization/Section3 -name '*.lean' | sort` = **71 个模块**：

| 目录 | 模块数 |
|---|---|
| `Section3/T10/` | 7 |
| `Section3/T11/` | 30 |
| `Section3/T12/` | 7 |
| `Section3/T13/` | 7 |
| `Section3/T14/` | 1 |
| `Section3/T15/` | 4 |
| `Section3/T16/` | 4 |
| `Section3/T17/` | 6 |
| `Section3/T20/` | 1 |
| `Section3/T22/` | 4 |

删除 Section 3 的 `lib/lean` 与 `ir` 目录内编译产物后，以一条 `lake build` 命令重编全部 71 个模块，日志为 `tmp/section3_build.log`。

| 项 | 值 |
|---|---|
| 退出码 | **0** |
| 墙上时间 | **80.80 s** |
| error | **0** |
| Section 3 Built | **71 / 71** |
| Section 3 Replayed | **0** |
| warning 行 | **99** |
| `grep -c 'warning: NSFormalization/Section3/'` | **3** |
| `.olean` 落盘 | **71** |
| Section 3 `sorry` grep | **5**（均为文档文字，原文如下） |

Section 3 warning 原文：

```text
warning: NSFormalization/Section3/T16/Assembly.lean:327:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Section3/T16/Assembly.lean:332:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Section3/T16/Assembly.lean:362:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
```

`sorry` grep 原文：

```text
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:46:No `sorry`, no `axiom`; every declaration prints `[propext, Classical.choice, Quot.sound]`.
formalization/NSFormalization/Section3/T15/HaarBridge.lean:42:`T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`.  No `sorry`, no named
formalization/NSFormalization/Section3/T11/PairingBound.lean:91:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T12/HaarCube.lean:42:No `sorry`, no `axiom`, no `native_decide`, no named goal input.  Every
formalization/NSFormalization/Section3/T12/TameProduct.lean:59:No `sorry`, no axiom, no named `Prop` input: every statement below is
```

<details>
<summary>全部 99 条 warning 原文（省略行尾空格）</summary>

```text
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
warning: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:51: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:148:2: Try this:
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:263:23: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:268:9: Variable name `k` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:126:2: Try this:
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:627:18: `continuousOn_iff_continuous_restrict` has been deprecated: Use `continuousOn_iff_continuous_domRestrict` instead
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:766:2: Try this:
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:768:2: Try this:
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:839:21: `continuousOn_iff_continuous_restrict` has been deprecated: Use `continuousOn_iff_continuous_domRestrict` instead
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: Unused tactic linter: `ring` does nothing
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: this tactic is never executed
warning: NSFormalization/Paper1/LocalizationBoundary.lean:355:36: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/LocalizationBoundary.lean:361:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead
warning: NSFormalization/Paper1/PeriodicScalarForceEndpoints.lean:156:5: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
warning: NSFormalization/Paper1/PeriodicForceConvergence.lean:53:13: This simp argument is unused:
warning: NSFormalization/Paper1/PeriodicInsertionSupport.lean:129:13: Variable name `hr` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:45:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:72:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:43:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:44:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:69:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:70:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:85:5: Variable name `hT` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:118:5: Variable name `hT` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'
warning: ../vendor/HeliCorgi/Formal/R3StokesL2Operator.lean:111:2: Try this:
warning: ../vendor/HeliCorgi/Formal/R3L2ScalarAux.lean:26:2: Try this:
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:16: Variable name `ht0` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:30: Variable name `htT` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:16: Variable name `ht0` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:30: Variable name `htT` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:16: Variable name `ht0` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:30: Variable name `htT` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:16: Variable name `ht0` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:30: Variable name `htT` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:95:0: Definition `FlowMapUniformRestartPackage.toContinuationPackage` is a proposition; use `theorem` instead of `def`
warning: ../vendor/HeliCorgi/Formal/R3SobolevCarrier.lean:80:2: try 'simp' instead of 'simpa'
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:11: Variable name `x` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:13: Variable name `y` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:12: Variable name `c` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:14: Variable name `x` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
warning: NSFormalization/Section3/T16/Assembly.lean:327:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Section3/T16/Assembly.lean:332:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Section3/T16/Assembly.lean:362:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
```

</details>

<details>
<summary>模块清单（71）</summary>

```text
formalization/NSFormalization/Section3/T10/DatumBasics.lean
formalization/NSFormalization/Section3/T10/ForcePaths.lean
formalization/NSFormalization/Section3/T10/FourierCalculus.lean
formalization/NSFormalization/Section3/T10/Leray.lean
formalization/NSFormalization/Section3/T10/Parseval.lean
formalization/NSFormalization/Section3/T10/PeriodicData.lean
formalization/NSFormalization/Section3/T10/PhysicalBridge.lean
formalization/NSFormalization/Section3/T11/Assembly.lean
formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean
formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean
formalization/NSFormalization/Section3/T11/ConvolutionBound.lean
formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean
formalization/NSFormalization/Section3/T11/CriterionBridge.lean
formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean
formalization/NSFormalization/Section3/T11/EnergyIdentity.lean
formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean
formalization/NSFormalization/Section3/T11/ExtendsBeyond.lean
formalization/NSFormalization/Section3/T11/FlowConversion.lean
formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean
formalization/NSFormalization/Section3/T11/GalileanClasses.lean
formalization/NSFormalization/Section3/T11/HighOrder.lean
formalization/NSFormalization/Section3/T11/LocalExistence.lean
formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean
formalization/NSFormalization/Section3/T11/LocalTheory.lean
formalization/NSFormalization/Section3/T11/Maximal.lean
formalization/NSFormalization/Section3/T11/MeanIdentity.lean
formalization/NSFormalization/Section3/T11/MildClassical.lean
formalization/NSFormalization/Section3/T11/MildMomentum.lean
formalization/NSFormalization/Section3/T11/MildPressure.lean
formalization/NSFormalization/Section3/T11/PairingBound.lean
formalization/NSFormalization/Section3/T11/Persistence.lean
formalization/NSFormalization/Section3/T11/PhysicalRecovery.lean
formalization/NSFormalization/Section3/T11/Rescaling.lean
formalization/NSFormalization/Section3/T11/Restart.lean
formalization/NSFormalization/Section3/T11/RestartBeyond.lean
formalization/NSFormalization/Section3/T11/Transport.lean
formalization/NSFormalization/Section3/T11/Uniqueness.lean
formalization/NSFormalization/Section3/T12/Cutoff.lean
formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean
formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean
formalization/NSFormalization/Section3/T12/HaarCube.lean
formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean
formalization/NSFormalization/Section3/T12/SpectralGap.lean
formalization/NSFormalization/Section3/T12/TameProduct.lean
formalization/NSFormalization/Section3/T13/Assembly.lean
formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean
formalization/NSFormalization/Section3/T13/KernelComparison.lean
formalization/NSFormalization/Section3/T13/Localization.lean
formalization/NSFormalization/Section3/T13/LocalizationKernel.lean
formalization/NSFormalization/Section3/T13/TorusIdentity.lean
formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean
formalization/NSFormalization/Section3/T14/PacketEnergy.lean
formalization/NSFormalization/Section3/T15/Bridges.lean
formalization/NSFormalization/Section3/T15/HaarBridge.lean
formalization/NSFormalization/Section3/T15/ParsevalZero.lean
formalization/NSFormalization/Section3/T15/Scaling.lean
formalization/NSFormalization/Section3/T16/Assembly.lean
formalization/NSFormalization/Section3/T16/BallPotential.lean
formalization/NSFormalization/Section3/T16/LatticeLift.lean
formalization/NSFormalization/Section3/T16/LocalPotential.lean
formalization/NSFormalization/Section3/T17/CorrectionDeriv.lean
formalization/NSFormalization/Section3/T17/CorrectionProfile.lean
formalization/NSFormalization/Section3/T17/ForceDeriv.lean
formalization/NSFormalization/Section3/T17/ForceProfile.lean
formalization/NSFormalization/Section3/T17/LatticeDeriv.lean
formalization/NSFormalization/Section3/T17/Transport.lean
formalization/NSFormalization/Section3/T20/CriticalRegularity.lean
formalization/NSFormalization/Section3/T22/Domain.lean
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean
formalization/NSFormalization/Section3/T22/RestrictBridge.lean
formalization/NSFormalization/Section3/T22/WeightRatio.lean
```

</details>

执行命令（模块列表由上述清单转换；Bash 数组将 71 个模块传入同一条 `lake build`）：

```sh
. scripts/lean-env.sh
find formalization/NSFormalization/Section3 -name '*.lean' | sort > tmp/section3_inventory.txt
find formalization/.lake/build/lib/lean/NSFormalization/Section3 -type f -delete
find formalization/.lake/build/ir/NSFormalization/Section3 -type f -delete
sed -e 's#formalization/##' -e 's#\.lean$##' -e 's#/#.#g' tmp/section3_inventory.txt > tmp/section3_modules.txt
cd verification
/usr/bin/time -f 'WALL_SECONDS=%e' -o ../tmp/section3_time.txt env LEAN_NUM_THREADS=6 bash -c 'mapfile -t modules < ../tmp/section3_modules.txt; lake build "${modules[@]}"' > ../tmp/section3_build.log 2>&1
```

计数命令：`grep -c 'error' tmp/section3_build.log` = 0；`grep -c 'warning' tmp/section3_build.log` = 99；`grep -c 'Built NSFormalization.Section3.' tmp/section3_build.log` = 71；`grep -c 'Replayed NSFormalization.Section3.' tmp/section3_build.log` = 0；`find formalization/.lake/build/lib/lean/NSFormalization/Section3 -name '*.olean' | wc -l` = 71。grep 无匹配时退出码为 1。

## 闸门

| 命令 | 退出码 | 结果 |
|---|---:|---|
| `make check` | 0 | `check_work_queue`: 45 work items consistent；13 policy tests OK |
| `make test` | 0 | **44** lines `checked; standard logical axioms only` |
| `make test-mutations` | 0 | implementation_refactor accepted；其余三项 rejected as required |
| `python3 experiments/check_contracts.py --base-ref main` | 0 | `registered_contracts: 42`; `base_compatibility_checked: true` |

四个闸门墙上时间分别为 9.86 s、2.08 s、13.47 s、4.92 s。台账 `collaboration/work_items.json` 已含 `T02.localization` 与 `T02.local_potential`；本次未修改台账。全量编译完成后才运行闸门；闸门完成后才运行 probe。

## Probe 与公理审计扫描

扫描集合为每个 `research/T1*/**/*_closes.lean`、`research/T1*/axioms_*.lean`、`research/T1*/probes/api_on_canonical.lean`，以及 `research/T11/probes/assembly_closes.lean`，去重后共 **124** 个文件。以 4 路并行、每个 `LEAN_NUM_THREADS=2` 执行 `cd verification && lake env lean ../<file>`：

| 项 | 值 |
|---|---:|
| 通过 | **124 / 124** |
| 失败 | **0** |
| 首个 error 行 | 无 |
| 公理结果 | `[propext, Classical.choice, Quot.sound]`（661 组；不同列表 0） |
| 其他公理名 | **0** |

公理名归一化为每行一个后，`grep -Evc '^(propext|Classical.choice|Quot.sound)$' tmp/axiom_names.txt` 输出 `0`（无匹配时 grep 退出码 1）。公理扫描先合并跨行的 `depends on axioms: [...]`，逐名与三个标准公理比较；结果保存在 `tmp/axiom_scan.json`。指定的 `T1*` 扫描范围不含 T20/T22。

<details>
<summary>逐文件退出码</summary>

| 文件 | 退出码 |
|---|---:|
| `research/T10/axioms_contract.lean` | 0 |
| `research/T10/axioms_datum_basics.lean` | 0 |
| `research/T10/axioms_force_paths.lean` | 0 |
| `research/T10/axioms_fourier_calculus.lean` | 0 |
| `research/T10/axioms_leray.lean` | 0 |
| `research/T10/axioms_parseval.lean` | 0 |
| `research/T10/axioms_physical_bridge.lean` | 0 |
| `research/T10/probes/api_on_canonical.lean` | 0 |
| `research/T10/probes/datum_basics_closes.lean` | 0 |
| `research/T10/probes/leray_closes.lean` | 0 |
| `research/T10/probes/parseval_closes.lean` | 0 |
| `research/T10/probes/physical_bridge_closes.lean` | 0 |
| `research/T11/axioms_assembly.lean` | 0 |
| `research/T11/axioms_classical_assembly.lean` | 0 |
| `research/T11/axioms_classical_regularity.lean` | 0 |
| `research/T11/axioms_convolution_bound.lean` | 0 |
| `research/T11/axioms_convolution_bound_real.lean` | 0 |
| `research/T11/axioms_criterion_bridge.lean` | 0 |
| `research/T11/axioms_duhamel_half_step.lean` | 0 |
| `research/T11/axioms_energy_identity.lean` | 0 |
| `research/T11/axioms_existence_input_h3.lean` | 0 |
| `research/T11/axioms_existence_probe.lean` | 0 |
| `research/T11/axioms_existence_u9b.lean` | 0 |
| `research/T11/axioms_extends_beyond.lean` | 0 |
| `research/T11/axioms_flow_conversion.lean` | 0 |
| `research/T11/axioms_fractional_smoothing.lean` | 0 |
| `research/T11/axioms_galilean_classes.lean` | 0 |
| `research/T11/axioms_high_order.lean` | 0 |
| `research/T11/axioms_maximal.lean` | 0 |
| `research/T11/axioms_mean_identity.lean` | 0 |
| `research/T11/axioms_mild_classical.lean` | 0 |
| `research/T11/axioms_mild_momentum.lean` | 0 |
| `research/T11/axioms_mild_pressure.lean` | 0 |
| `research/T11/axioms_pairing_bound.lean` | 0 |
| `research/T11/axioms_persistence.lean` | 0 |
| `research/T11/axioms_physical_recovery.lean` | 0 |
| `research/T11/axioms_rescaling.lean` | 0 |
| `research/T11/axioms_restart.lean` | 0 |
| `research/T11/axioms_restart_beyond.lean` | 0 |
| `research/T11/axioms_transport.lean` | 0 |
| `research/T11/axioms_uniqueness.lean` | 0 |
| `research/T11/probes/api_on_canonical.lean` | 0 |
| `research/T11/probes/assembly_closes.lean` | 0 |
| `research/T11/probes/classical_assembly_closes.lean` | 0 |
| `research/T11/probes/classical_regularity_closes.lean` | 0 |
| `research/T11/probes/convolution_bound_closes.lean` | 0 |
| `research/T11/probes/convolution_bound_real_closes.lean` | 0 |
| `research/T11/probes/criterion_bridge_closes.lean` | 0 |
| `research/T11/probes/duhamel_half_step_closes.lean` | 0 |
| `research/T11/probes/energy_identity_closes.lean` | 0 |
| `research/T11/probes/existence_input_h3_closes.lean` | 0 |
| `research/T11/probes/extends_beyond_closes.lean` | 0 |
| `research/T11/probes/fractional_smoothing_closes.lean` | 0 |
| `research/T11/probes/galilean_classes_closes.lean` | 0 |
| `research/T11/probes/high_order_closes.lean` | 0 |
| `research/T11/probes/maximal_closes.lean` | 0 |
| `research/T11/probes/mean_identity_closes.lean` | 0 |
| `research/T11/probes/mild_classical_closes.lean` | 0 |
| `research/T11/probes/mild_momentum_closes.lean` | 0 |
| `research/T11/probes/mild_pressure_closes.lean` | 0 |
| `research/T11/probes/pairing_bound_closes.lean` | 0 |
| `research/T11/probes/persistence_closes.lean` | 0 |
| `research/T11/probes/physical_recovery_closes.lean` | 0 |
| `research/T11/probes/rescaling_closes.lean` | 0 |
| `research/T11/probes/restart_beyond_closes.lean` | 0 |
| `research/T11/probes/restart_closes.lean` | 0 |
| `research/T11/probes/transport_closes.lean` | 0 |
| `research/T11/probes/uniqueness_closes.lean` | 0 |
| `research/T12/axioms_cutoff.lean` | 0 |
| `research/T12/axioms_fourier_embeddings.lean` | 0 |
| `research/T12/axioms_haar_cube.lean` | 0 |
| `research/T12/axioms_spectral_gap.lean` | 0 |
| `research/T12/axioms_tame_product.lean` | 0 |
| `research/T12/axioms_u3.lean` | 0 |
| `research/T12/probes/api_on_canonical.lean` | 0 |
| `research/T12/probes/cutoff_closes.lean` | 0 |
| `research/T12/probes/cutoff_gagliardo_closes.lean` | 0 |
| `research/T12/probes/fourier_embeddings_closes.lean` | 0 |
| `research/T12/probes/haar_cube_closes.lean` | 0 |
| `research/T12/probes/spectral_gap_closes.lean` | 0 |
| `research/T12/probes/tame_product_closes.lean` | 0 |
| `research/T13/axioms_assembly.lean` | 0 |
| `research/T13/axioms_constant_endpoints.lean` | 0 |
| `research/T13/axioms_contract.lean` | 0 |
| `research/T13/axioms_kernel_comparison.lean` | 0 |
| `research/T13/axioms_localization_kernel.lean` | 0 |
| `research/T13/axioms_torus_identity.lean` | 0 |
| `research/T13/axioms_wholespace_identity.lean` | 0 |
| `research/T13/probes/api_on_canonical.lean` | 0 |
| `research/T13/probes/assembly_closes.lean` | 0 |
| `research/T13/probes/constant_endpoints_closes.lean` | 0 |
| `research/T13/probes/kernel_comparison_closes.lean` | 0 |
| `research/T13/probes/localization_kernel_closes.lean` | 0 |
| `research/T13/probes/torus_identity_closes.lean` | 0 |
| `research/T13/probes/wholespace_identity_closes.lean` | 0 |
| `research/T14/axioms_contract.lean` | 0 |
| `research/T14/axioms_packet_energy.lean` | 0 |
| `research/T14/probes/api_on_canonical.lean` | 0 |
| `research/T15/axioms_u1.lean` | 0 |
| `research/T15/axioms_ucan.lean` | 0 |
| `research/T15/axioms_utb1.lean` | 0 |
| `research/T15/axioms_utb2.lean` | 0 |
| `research/T15/probes/api_on_canonical.lean` | 0 |
| `research/T15/probes/haar_bridge_closes.lean` | 0 |
| `research/T15/probes/parseval_zero_closes.lean` | 0 |
| `research/T16/axioms_assembly.lean` | 0 |
| `research/T16/axioms_ball_potential.lean` | 0 |
| `research/T16/axioms_contract.lean` | 0 |
| `research/T16/axioms_lattice_lift.lean` | 0 |
| `research/T16/axioms_local_potential.lean` | 0 |
| `research/T16/probes/api_on_canonical.lean` | 0 |
| `research/T16/probes/assembly_closes.lean` | 0 |
| `research/T16/probes/ball_potential_closes.lean` | 0 |
| `research/T16/probes/lattice_lift_closes.lean` | 0 |
| `research/T17/axioms_u1.lean` | 0 |
| `research/T17/axioms_u2.lean` | 0 |
| `research/T17/axioms_u3.lean` | 0 |
| `research/T17/axioms_u4.lean` | 0 |
| `research/T17/axioms_u5u6.lean` | 0 |
| `research/T17/probes/correction_profile_closes.lean` | 0 |
| `research/T17/probes/derivative_bounds_closes.lean` | 0 |
| `research/T17/probes/force_profile_closes.lean` | 0 |
| `research/T17/probes/lattice_deriv_closes.lean` | 0 |
| `research/T17/probes/transport_closes.lean` | 0 |

</details>

## 结论

71 个 Section 3 模块从清空后的产物目录重新 Built 71 个，退出码 0，Section 3 warning 3；全局日志有 99 条含 warning 的行。四个闸门退出码分别为 0/0/0/0，`make test` 输出 44 条标准公理检查行，合同注册检查报告 42。124/124 个 probe/axioms 文件通过；公理扫描共 661 组，其他公理名 0；源码 `sorry` grep 命中 5 处。

未全绿项目：

- 全局日志含 warning 的行 99 条，原文见上；其中 Section 3 3 条。
- Section 3 `sorry` grep 计数为 5，均为说明文字，原文见上。

## 四段记录

**检查了什么：** Section 3 71 模块全量重编、四个闸门、124 个 probe/axioms 文件及公理扫描；被检提交 `dbdac830cec09b6cd3d2aa81823e67a0051ddb70`。

**树中现在有什么：** T10/T11/T12/T13/T14/T15/T16/T17/T20/T22 分别 7/30/7/7/1/4/4/6/1/4 个模块；71 个 `.olean`；42 个注册合同。仅新增本报告与 `research/MAINT/REPORT_399.md`；未改 Lean 源码或台账。

**什么不绿：** 全局日志 99 条含 warning 的行（原文见完整报告）；Section 3 warning 3；`sorry` grep 5 处文档命中，原文：

```text
warning: NSFormalization/Section3/T16/Assembly.lean:327:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Section3/T16/Assembly.lean:332:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Section3/T16/Assembly.lean:362:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:46:No `sorry`, no `axiom`; every declaration prints `[propext, Classical.choice, Quot.sound]`.
formalization/NSFormalization/Section3/T15/HaarBridge.lean:42:`T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`.  No `sorry`, no named
formalization/NSFormalization/Section3/T11/PairingBound.lean:91:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T12/HaarCube.lean:42:No `sorry`, no `axiom`, no `native_decide`, no named goal input.  Every
formalization/NSFormalization/Section3/T12/TameProduct.lean:59:No `sorry`, no axiom, no named `Prop` input: every statement below is
```

**命令及结果：** `lake build` rc 0，WALL_SECONDS=80.80，71 Built、0 Replayed、0 error；`make check`/`make test`/`make test-mutations`/`check_contracts.py --base-ref main` rc 0/0/0/0；`make test` 标准公理检查行 44（不是注册合同数量）；probe 124/124 通过，其他公理名 0。
