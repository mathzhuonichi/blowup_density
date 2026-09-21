# Section 3 集成分支全量编译检查（2026-09-19）

目的：验证当前被检提交在 T21 注册后的 Section 3 全部模块可在同一源码树编译；只读检查。

## 环境

| 项 | 值 |
|---|---|
| 被检提交 | `a86a5b76ab821838d2eca734e5da91f0065d1ba3` |
| worktree | `.claude/worktrees/479-MAINT-section3-build-h` |
| 工具链 | Lean 4.34.0-rc2 (`6a10ac8c22be`) |
| 线程 | `LEAN_NUM_THREADS=6` |
| 运行方式 | `. scripts/lean-env.sh`；`lake` 从 `verification/` 执行 |

## Section 3 模块数与全量编译

`find formalization/NSFormalization/Section3 -name '*.lean' | sort` = **167 个模块**：

| 目录 | 模块数 |
|---|---|
| `Section3/T10/` | 7 |
| `Section3/T11/` | 30 |
| `Section3/T12/` | 12 |
| `Section3/T13/` | 7 |
| `Section3/T14/` | 1 |
| `Section3/T15/` | 18 |
| `Section3/T16/` | 4 |
| `Section3/T17/` | 15 |
| `Section3/T18/` | 12 |
| `Section3/T19/` | 7 |
| `Section3/T20/` | 13 |
| `Section3/T21/` | 11 |
| `Section3/T22/` | 12 |
| `Section3/T24/` | 18 |

删除 Section 3 的 `lib/lean` 与 `ir` 目录内编译产物后，以一条 `lake build` 命令重编全部 167 个模块，日志为 `tmp/section3_build.log`。

| 项 | 值 |
|---|---|
| 退出码 | **0** |
| 墙上时间 | **148.47 s** |
| error | **0** |
| Section 3 Built | **167 / 167** |
| Section 3 Replayed | **0** |
| warning 行 | **108** |
| `grep -c 'warning: NSFormalization/Section3/'` | **1** |
| `.olean` 落盘 | **167** |
| Section 3 `sorry` grep | **16**（均为文档文字） |

Section 3 warning 原文：

```text
warning: NSFormalization/Section3/T22/Assembly.lean:24:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
```

`sorry` grep 原文：

```text
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:46:No `sorry`, no `axiom`; every declaration prints `[propext, Classical.choice, Quot.sound]`.
formalization/NSFormalization/Section3/T22/OrderZero.lean:38:No `sorry`/`axiom`/`native_decide`; every declaration prints `[propext, Classical.choice,
formalization/NSFormalization/Section3/T22/CutoffDatum.lean:44:No `sorry`/`axiom`/`native_decide`; every declaration prints
formalization/NSFormalization/Section3/T15/Energy.lean:42:No `sorry`, no named input, no new mathematical alias.
formalization/NSFormalization/Section3/T15/Mixed.lean:42:No `sorry`, no named input, no new mathematical alias.
formalization/NSFormalization/Section3/T15/HaarBridge.lean:42:`T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`.  No `sorry`, no named
formalization/NSFormalization/Section3/T11/PairingBound.lean:91:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T12/GradientLSix.lean:41:No `sorry`, no `axiom`, no `native_decide`, no named goal input; every declaration
formalization/NSFormalization/Section3/T12/CriticalL3Density.lean:50:No `sorry`, no `axiom`, no `native_decide`, no `maxHeartbeats` override, no named
formalization/NSFormalization/Section3/T12/HaarCube.lean:42:No `sorry`, no `axiom`, no `native_decide`, no named goal input.  Every
formalization/NSFormalization/Section3/T12/TameProduct.lean:59:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T20/H1Energy.lean:44:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
formalization/NSFormalization/Section3/T20/H1Trilinear.lean:76:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean:52:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
formalization/NSFormalization/Section3/T20/CriticalEnergy.lean:39:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
formalization/NSFormalization/Section3/T20/Continuation.lean:42:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
```

执行命令：

```sh
. scripts/lean-env.sh
find formalization/.lake/build/lib/lean/NSFormalization/Section3 -type f -delete
find formalization/.lake/build/ir/NSFormalization/Section3 -type f -delete
find formalization/NSFormalization/Section3 -name '*.lean' | sort | sed -e 's#formalization/##' -e 's#\.lean$##' -e 's#/#.#g' > tmp/section3_modules_h.txt
cd verification
/usr/bin/time -f 'WALL_SECONDS=%e' -o ../tmp/section3_time_h.txt env LEAN_NUM_THREADS=6 lake build $(cat ../tmp/section3_modules_h.txt) > ../tmp/section3_build.log 2>&1
```

<details>
<summary>模块清单（167）</summary>

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
formalization/NSFormalization/Section3/T12/CriticalL3.lean
formalization/NSFormalization/Section3/T12/CriticalL3Density.lean
formalization/NSFormalization/Section3/T12/Cutoff.lean
formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean
formalization/NSFormalization/Section3/T12/DirDeriv.lean
formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean
formalization/NSFormalization/Section3/T12/GradientLSix.lean
formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean
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
formalization/NSFormalization/Section3/T15/Assembly.lean
formalization/NSFormalization/Section3/T15/Blowup.lean
formalization/NSFormalization/Section3/T15/Bridges.lean
formalization/NSFormalization/Section3/T15/Convergence.lean
formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean
formalization/NSFormalization/Section3/T15/Energy.lean
formalization/NSFormalization/Section3/T15/Equation.lean
formalization/NSFormalization/Section3/T15/ForceMem.lean
formalization/NSFormalization/Section3/T15/HaarBridge.lean
formalization/NSFormalization/Section3/T15/Mixed.lean
formalization/NSFormalization/Section3/T15/ParsevalZero.lean
formalization/NSFormalization/Section3/T15/Placement.lean
formalization/NSFormalization/Section3/T15/Pressure.lean
formalization/NSFormalization/Section3/T15/Scaling.lean
formalization/NSFormalization/Section3/T15/SingleCopy.lean
formalization/NSFormalization/Section3/T15/SobolevBound.lean
formalization/NSFormalization/Section3/T15/SobolevPath.lean
formalization/NSFormalization/Section3/T15/Solution.lean
formalization/NSFormalization/Section3/T16/Assembly.lean
formalization/NSFormalization/Section3/T16/BallPotential.lean
formalization/NSFormalization/Section3/T16/LatticeLift.lean
formalization/NSFormalization/Section3/T16/LocalPotential.lean
formalization/NSFormalization/Section3/T17/Assembly.lean
formalization/NSFormalization/Section3/T17/Correction.lean
formalization/NSFormalization/Section3/T17/CorrectionDeriv.lean
formalization/NSFormalization/Section3/T17/CorrectionProfile.lean
formalization/NSFormalization/Section3/T17/Energy.lean
formalization/NSFormalization/Section3/T17/ForceDeriv.lean
formalization/NSFormalization/Section3/T17/ForceProfile.lean
formalization/NSFormalization/Section3/T17/ForceSupport.lean
formalization/NSFormalization/Section3/T17/ForceVolume.lean
formalization/NSFormalization/Section3/T17/LatticeDeriv.lean
formalization/NSFormalization/Section3/T17/Mixed.lean
formalization/NSFormalization/Section3/T17/SlabBridge.lean
formalization/NSFormalization/Section3/T17/SlabBridge2.lean
formalization/NSFormalization/Section3/T17/Sobolev.lean
formalization/NSFormalization/Section3/T17/Transport.lean
formalization/NSFormalization/Section3/T18/Assembly.lean
formalization/NSFormalization/Section3/T18/CrossTransport.lean
formalization/NSFormalization/Section3/T18/Divergence.lean
formalization/NSFormalization/Section3/T18/EnergyRate.lean
formalization/NSFormalization/Section3/T18/ForceClass.lean
formalization/NSFormalization/Section3/T18/Insertion.lean
formalization/NSFormalization/Section3/T18/Kinematics.lean
formalization/NSFormalization/Section3/T18/Lifespan.lean
formalization/NSFormalization/Section3/T18/MixedRate.lean
formalization/NSFormalization/Section3/T18/Momentum.lean
formalization/NSFormalization/Section3/T18/SobolevRate.lean
formalization/NSFormalization/Section3/T18/Support.lean
formalization/NSFormalization/Section3/T19/Assembly.lean
formalization/NSFormalization/Section3/T19/Bookkeeping.lean
formalization/NSFormalization/Section3/T19/Closure.lean
formalization/NSFormalization/Section3/T19/Density.lean
formalization/NSFormalization/Section3/T19/DensityEngine.lean
formalization/NSFormalization/Section3/T19/Projection.lean
formalization/NSFormalization/Section3/T19/Threading.lean
formalization/NSFormalization/Section3/T20/Assembly.lean
formalization/NSFormalization/Section3/T20/BIntegral.lean
formalization/NSFormalization/Section3/T20/ConstantTransport.lean
formalization/NSFormalization/Section3/T20/Continuation.lean
formalization/NSFormalization/Section3/T20/CriticalEnergy.lean
formalization/NSFormalization/Section3/T20/CriticalRegularity.lean
formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean
formalization/NSFormalization/Section3/T20/GlobalRegularity.lean
formalization/NSFormalization/Section3/T20/H1Energy.lean
formalization/NSFormalization/Section3/T20/H1Trilinear.lean
formalization/NSFormalization/Section3/T20/MeanReduction.lean
formalization/NSFormalization/Section3/T20/TransportLambda.lean
formalization/NSFormalization/Section3/T20/YBound.lean
formalization/NSFormalization/Section3/T21/Assembly.lean
formalization/NSFormalization/Section3/T21/Ball.lean
formalization/NSFormalization/Section3/T21/CriticalBridge.lean
formalization/NSFormalization/Section3/T21/Definitions.lean
formalization/NSFormalization/Section3/T21/Disjointness.lean
formalization/NSFormalization/Section3/T21/ForceMonotonicity.lean
formalization/NSFormalization/Section3/T21/Main.lean
formalization/NSFormalization/Section3/T21/MainAssembly.lean
formalization/NSFormalization/Section3/T21/NonDensity.lean
formalization/NSFormalization/Section3/T21/OrderLowering.lean
formalization/NSFormalization/Section3/T21/Zero.lean
formalization/NSFormalization/Section3/T22/Assembly.lean
formalization/NSFormalization/Section3/T22/CutoffDatum.lean
formalization/NSFormalization/Section3/T22/CutoffKernel.lean
formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean
formalization/NSFormalization/Section3/T22/CutoffMultiplierField.lean
formalization/NSFormalization/Section3/T22/Domain.lean
formalization/NSFormalization/Section3/T22/OrderZero.lean
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean
formalization/NSFormalization/Section3/T22/RestrictBridge.lean
formalization/NSFormalization/Section3/T22/WeightRatio.lean
formalization/NSFormalization/Section3/T22/ZeroExtRegularity.lean
formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean
formalization/NSFormalization/Section3/T24/AffineAssembly.lean
formalization/NSFormalization/Section3/T24/AffineBasics.lean
formalization/NSFormalization/Section3/T24/AffineDivergence.lean
formalization/NSFormalization/Section3/T24/AffineEnergy.lean
formalization/NSFormalization/Section3/T24/AffineFamily.lean
formalization/NSFormalization/Section3/T24/AffineForce.lean
formalization/NSFormalization/Section3/T24/AffineMomentum.lean
formalization/NSFormalization/Section3/T24/AffineNonisolated.lean
formalization/NSFormalization/Section3/T24/AffineSpeed.lean
formalization/NSFormalization/Section3/T24/AffineWitness.lean
formalization/NSFormalization/Section3/T24/Conservative.lean
formalization/NSFormalization/Section3/T24/ConservativeAssembly.lean
formalization/NSFormalization/Section3/T24/Multiple.lean
formalization/NSFormalization/Section3/T24/MultipleAssembled.lean
formalization/NSFormalization/Section3/T24/MultipleAssembly.lean
formalization/NSFormalization/Section3/T24/MultipleComponents.lean
formalization/NSFormalization/Section3/T24/MultipleRegions.lean
formalization/NSFormalization/Section3/T24/PotentialPairing.lean
```

</details>

## 闸门

| 命令 | 退出码 | 结果 |
|---|---:|---|
| `make check` | 0 | `check_work_queue`: 45 work items consistent；13 policy tests OK；`source_hashes_match: false`；本次无 `--base-ref` 时 `base_compatibility_checked: false` |
| `make test` | 0 | **66** lines `checked; standard logical axioms only`（54 个注册合同） |
| `make test-mutations` | 0 | implementation_refactor accepted；其余三项 rejected as required |
| `python3 experiments/check_contracts.py --base-ref main` | 0 | `registered_contracts: 54`; `base_compatibility_checked: true` |

四个闸门墙上时间分别为 10.32 s、7.06 s、13.21 s、4.99 s。`make test` 的 66 行来自测试模块中检查的声明行数；注册合同数由 `check_contracts.py` 报告为 54。

## Probe 与公理审计扫描

扫描集合为每个 `research/T1*/**/*_closes.lean`、`research/T1*/axioms_*.lean`、`research/T1*/probes/api_on_canonical.lean`，以及每个 `research/T2*/probes/*.lean`、`research/T2*/axioms_*.lean`，去重后共 **339** 个文件（T1* 199，T2* 140）。以 4 路并行、每个 `LEAN_NUM_THREADS=2` 执行 `cd verification && lake env lean ../<file>`；墙上时间 256.85 s：

| 项 | 值 |
|---|---:|
| 通过 | **298 / 339** |
| 预期失败 | **41**（命名模式 33；已有审稿记录 8） |
| 非预期失败 | **0** |
| 首个 error 行 | 41 个预期失败的原文见下 |
| 公理结果 | `[propext, Classical.choice, Quot.sound]`（2106 组；不同列表 0） |
| 其他公理名 | **0** |

33 个失败文件匹配任务指定的 `rev*_mutation*.lean` / `*negative*.lean` / `*widen*` / `*_sign_*` 模式。另 8 个失败文件是已有审稿记录明确保留的 negative/mutation/rejection probe：`rev441_doubled_radius.lean`、`rev397_field_target.lean`、`rev395_mutated_constant.lean`、`rev398_wrong_viscous_sign.lean`、`rev402_divergence_one.lean`、`rev407_mutated_time.lean`、`rev469_wrong_dissipation_constant.lean`、`rev471_wrong_dissipation_constant.lean`。41 个预期失败不计为红项。

预期失败的首个 error 行原文：

```text
../research/T20/probes/rev381_negative_constant.lean:9:2: error: Type mismatch
../research/T20/probes/rev389_negative.lean:27:2: error: Type mismatch
../research/T20/probes/rev390_sign_flip.lean:33:2: error: Type mismatch
../research/T20/probes/rev413_negative.lean:19:2: error: Type mismatch
../research/T20/probes/rev415_mutation.lean:17:2: error: Type mismatch
../research/T20/probes/rev428_negative.lean:16:2: error: Type mismatch
../research/T20/probes/rev429_negative_const.lean:24:2: error: Type mismatch
../research/T20/probes/rev432_negative.lean:14:2: error: Type mismatch
../research/T20/probes/rev437_negative.lean:14:70: error: unsolved goals
../research/T20/probes/rev441_doubled_radius.lean:20:2: error: Type mismatch
../research/T20/probes/rev451_widen_smallness_mutation.lean:17:55: error: Application type mismatch: The argument
../research/T20/probes/rev452_negative_sign.lean:30:81: error: unsolved goals
../research/T21/probes/rev472_negative.lean:19:2: error: Type mismatch
../research/T21/probes/rev474_mutation.lean:20:2: error: Type mismatch
../research/T21/probes/rev475_main_threshold_mutation.lean:17:2: error: Type mismatch
../research/T22/probes/rev383_negative.lean:18:2: error: Type mismatch
../research/T22/probes/rev386_mutation.lean:16:32: error: unsolved goals
../research/T22/probes/rev387_mutation_constant.lean:15:2: error: Type mismatch
../research/T22/probes/rev391_mutation.lean:42:9: error: invalid 'calc' step, left-hand side is
../research/T22/probes/rev393_mutation.lean:225:23: error: typeclass instance problem is stuck
../research/T22/probes/rev397_field_target.lean:18:8: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section3.T22.cutoffMultiplier`
../research/T22/probes/rev397_mutation.lean:17:2: error: Type mismatch
../research/T22/probes/rev406_mutation.lean:13:2: error: Type mismatch: After simplification, term
../research/T22/probes/rev408_mutation.lean:25:27: error: unsolved goals
../research/T22/probes/rev409_mutation_constant.lean:18:2: error: Type mismatch: After simplification, term
../research/T22/probes/rev418_negative.lean:14:2: error: Type mismatch
../research/T22/probes/rev423_negative.lean:21:2: error: Type mismatch: After simplification, term
../research/T24/probes/rev392_widened_interval.lean:21:42: error: Application type mismatch: The argument
../research/T24/probes/rev395_mutated_constant.lean:26:2: error: Type mismatch
../research/T24/probes/rev398_negative.lean:9:84: error: unsolved goals
../research/T24/probes/rev398_wrong_viscous_sign.lean:37:2: error: Tactic `rfl` failed: The left-hand side
../research/T24/probes/rev402_divergence_one.lean:29:58: error: unsolved goals
../research/T24/probes/rev403_negative_speed.lean:42:4: error: Type mismatch
../research/T24/probes/rev407_mutated_time.lean:15:2: error: Type mismatch
../research/T24/probes/rev414_mutation.lean:13:39: error: linarith failed to find a contradiction
../research/T24/probes/rev420_negative_interval.lean:22:62: error: Application type mismatch: The argument
../research/T24/probes/rev430_mutation.lean:9:41: error: Application type mismatch: The argument
../research/T24/probes/rev467_negative_eps_time.lean:16:2: error: Type mismatch
../research/T24/probes/rev468_mutation.lean:19:2: error: Type mismatch
../research/T24/probes/rev469_wrong_dissipation_constant.lean:22:2: error: Type mismatch
../research/T24/probes/rev471_wrong_dissipation_constant.lean:18:2: error: Type mismatch
```

公理扫描合并了跨行的 `depends on axioms: [...]`，逐名与三个标准公理比较；结果保存在 `tmp/axiom_scan_h.json`。

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
| `research/T12/axioms_u4.lean` | 0 |
| `research/T12/axioms_u4b.lean` | 0 |
| `research/T12/axioms_u5.lean` | 0 |
| `research/T12/axioms_u6.lean` | 0 |
| `research/T12/axioms_ureg.lean` | 0 |
| `research/T12/probes/api_on_canonical.lean` | 0 |
| `research/T12/probes/critical_l3_closes.lean` | 0 |
| `research/T12/probes/critical_l3_density_closes.lean` | 0 |
| `research/T12/probes/cutoff_closes.lean` | 0 |
| `research/T12/probes/cutoff_gagliardo_closes.lean` | 0 |
| `research/T12/probes/fourier_embeddings_closes.lean` | 0 |
| `research/T12/probes/gradient_l6_closes.lean` | 0 |
| `research/T12/probes/gradient_lambda_l3_closes.lean` | 0 |
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
| `research/T15/axioms_u10.lean` | 0 |
| `research/T15/axioms_u11.lean` | 0 |
| `research/T15/axioms_u12_u13.lean` | 0 |
| `research/T15/axioms_u14.lean` | 0 |
| `research/T15/axioms_u14b.lean` | 0 |
| `research/T15/axioms_u15.lean` | 0 |
| `research/T15/axioms_u2.lean` | 0 |
| `research/T15/axioms_u3.lean` | 0 |
| `research/T15/axioms_u4_u5.lean` | 0 |
| `research/T15/axioms_u6_u7.lean` | 0 |
| `research/T15/axioms_u8.lean` | 0 |
| `research/T15/axioms_u9.lean` | 0 |
| `research/T15/axioms_ucan.lean` | 0 |
| `research/T15/axioms_utb1.lean` | 0 |
| `research/T15/axioms_utb2.lean` | 0 |
| `research/T15/probes/api_on_canonical.lean` | 0 |
| `research/T15/probes/assembly_closes.lean` | 0 |
| `research/T15/probes/blowup_force_mem_closes.lean` | 0 |
| `research/T15/probes/convergence_closes.lean` | 0 |
| `research/T15/probes/convergence_two_closes.lean` | 0 |
| `research/T15/probes/energy_mixed_closes.lean` | 0 |
| `research/T15/probes/equation_closes.lean` | 0 |
| `research/T15/probes/haar_bridge_closes.lean` | 0 |
| `research/T15/probes/parseval_zero_closes.lean` | 0 |
| `research/T15/probes/placement_closes.lean` | 0 |
| `research/T15/probes/pressure_closes.lean` | 0 |
| `research/T15/probes/single_copy_closes.lean` | 0 |
| `research/T15/probes/sobolev_bound_closes.lean` | 0 |
| `research/T15/probes/sobolev_path_closes.lean` | 0 |
| `research/T15/probes/solution_closes.lean` | 0 |
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
| `research/T17/axioms_u10.lean` | 0 |
| `research/T17/axioms_u11.lean` | 0 |
| `research/T17/axioms_u12.lean` | 0 |
| `research/T17/axioms_u13.lean` | 0 |
| `research/T17/axioms_u2.lean` | 0 |
| `research/T17/axioms_u3.lean` | 0 |
| `research/T17/axioms_u4.lean` | 0 |
| `research/T17/axioms_u5u6.lean` | 0 |
| `research/T17/axioms_u7.lean` | 0 |
| `research/T17/axioms_u8.lean` | 0 |
| `research/T17/axioms_u9.lean` | 0 |
| `research/T17/axioms_ucan.lean` | 0 |
| `research/T17/probes/correction_profile_closes.lean` | 0 |
| `research/T17/probes/derivative_bounds_closes.lean` | 0 |
| `research/T17/probes/energy_closes.lean` | 0 |
| `research/T17/probes/force_profile_closes.lean` | 0 |
| `research/T17/probes/force_support_closes.lean` | 0 |
| `research/T17/probes/force_volume_closes.lean` | 0 |
| `research/T17/probes/lattice_deriv_closes.lean` | 0 |
| `research/T17/probes/mixed_closes.lean` | 0 |
| `research/T17/probes/sobolev_closes.lean` | 0 |
| `research/T17/probes/transport_closes.lean` | 0 |
| `research/T18/axioms_u1.lean` | 0 |
| `research/T18/axioms_u11.lean` | 0 |
| `research/T18/axioms_u12.lean` | 0 |
| `research/T18/axioms_u2_u4.lean` | 0 |
| `research/T18/axioms_u5_u6.lean` | 0 |
| `research/T18/axioms_u7.lean` | 0 |
| `research/T18/axioms_u8.lean` | 0 |
| `research/T18/axioms_u9_u10.lean` | 0 |
| `research/T18/probes/insertion_closes.lean` | 0 |
| `research/T18/probes/u11_closes.lean` | 0 |
| `research/T18/probes/u2_u4_closes.lean` | 0 |
| `research/T18/probes/u5_u6_closes.lean` | 0 |
| `research/T18/probes/u7_closes.lean` | 0 |
| `research/T18/probes/u8_closes.lean` | 0 |
| `research/T18/probes/u9_u10_closes.lean` | 0 |
| `research/T19/axioms_u0.lean` | 0 |
| `research/T19/axioms_u10_u12.lean` | 0 |
| `research/T19/axioms_u13_u14.lean` | 0 |
| `research/T19/axioms_u15.lean` | 0 |
| `research/T19/axioms_u1_6.lean` | 0 |
| `research/T19/axioms_u7_u9.lean` | 0 |
| `research/T19/axioms_ucan.lean` | 0 |
| `research/T19/probes/api_on_canonical.lean` | 0 |
| `research/T19/probes/assembly_closes.lean` | 0 |
| `research/T19/probes/bookkeeping_closes.lean` | 0 |
| `research/T19/probes/closure_closes.lean` | 0 |
| `research/T19/probes/density_engine_closes.lean` | 0 |
| `research/T19/probes/projection_closes.lean` | 0 |
| `research/T19/probes/threading_closes.lean` | 0 |
| `research/T20/axioms_canonical.lean` | 0 |
| `research/T20/axioms_u10a.lean` | 0 |
| `research/T20/axioms_u10b.lean` | 0 |
| `research/T20/axioms_u11.lean` | 0 |
| `research/T20/axioms_u12.lean` | 0 |
| `research/T20/axioms_u13.lean` | 0 |
| `research/T20/axioms_u1_2_6.lean` | 0 |
| `research/T20/axioms_u3_u4.lean` | 0 |
| `research/T20/axioms_u5.lean` | 0 |
| `research/T20/axioms_u7.lean` | 0 |
| `research/T20/axioms_u8.lean` | 0 |
| `research/T20/axioms_u9.lean` | 0 |
| `research/T20/probes/api_on_canonical.lean` | 0 |
| `research/T20/probes/bintegral_transport_closes.lean` | 0 |
| `research/T20/probes/continuation_closes.lean` | 0 |
| `research/T20/probes/critical_energy_closes.lean` | 0 |
| `research/T20/probes/critical_trilinear_closes.lean` | 0 |
| `research/T20/probes/global_regularity_closes.lean` | 0 |
| `research/T20/probes/h1_energy_closes.lean` | 0 |
| `research/T20/probes/h1_trilinear_closes.lean` | 0 |
| `research/T20/probes/mean_reduction_closes.lean` | 0 |
| `research/T20/probes/rev381_negative_constant.lean` | 1 |
| `research/T20/probes/rev381_nonvacuity.lean` | 0 |
| `research/T20/probes/rev389_negative.lean` | 1 |
| `research/T20/probes/rev390_nonvacuity.lean` | 0 |
| `research/T20/probes/rev390_sign_flip.lean` | 1 |
| `research/T20/probes/rev413_negative.lean` | 1 |
| `research/T20/probes/rev415_mutation.lean` | 1 |
| `research/T20/probes/rev428_negative.lean` | 1 |
| `research/T20/probes/rev429_collision.lean` | 0 |
| `research/T20/probes/rev429_negative_const.lean` | 1 |
| `research/T20/probes/rev432_negative.lean` | 1 |
| `research/T20/probes/rev437_negative.lean` | 1 |
| `research/T20/probes/rev441_doubled_radius.lean` | 1 |
| `research/T20/probes/rev451_exact_and_nonvacuous.lean` | 0 |
| `research/T20/probes/rev451_widen_smallness_mutation.lean` | 1 |
| `research/T20/probes/rev452_negative_sign.lean` | 1 |
| `research/T20/probes/transport_lambda_closes.lean` | 0 |
| `research/T20/probes/ybound_closes.lean` | 0 |
| `research/T21/axioms_a.lean` | 0 |
| `research/T21/axioms_n0_n12.lean` | 0 |
| `research/T21/axioms_n11_n15.lean` | 0 |
| `research/T21/probes/assembly_closes.lean` | 0 |
| `research/T21/probes/main_closes.lean` | 0 |
| `research/T21/probes/nondensity_closes.lean` | 0 |
| `research/T21/probes/rev472_negative.lean` | 1 |
| `research/T21/probes/rev472_nonvacuity.lean` | 0 |
| `research/T21/probes/rev474_mutation.lean` | 1 |
| `research/T21/probes/rev474_nonvacuity.lean` | 0 |
| `research/T21/probes/rev475_main_threshold_mutation.lean` | 1 |
| `research/T21/probes/rev475_nonvacuity.lean` | 0 |
| `research/T22/axioms_ua1.lean` | 0 |
| `research/T22/axioms_ua2.lean` | 0 |
| `research/T22/axioms_ua3.lean` | 0 |
| `research/T22/axioms_ua3b.lean` | 0 |
| `research/T22/axioms_ua4.lean` | 0 |
| `research/T22/axioms_ua5.lean` | 0 |
| `research/T22/axioms_ub1.lean` | 0 |
| `research/T22/axioms_ub2.lean` | 0 |
| `research/T22/axioms_ub3.lean` | 0 |
| `research/T22/axioms_ureg.lean` | 0 |
| `research/T22/axioms_uz1.lean` | 0 |
| `research/T22/probes/api_on_canonical.lean` | 0 |
| `research/T22/probes/cutoff_datum_closes.lean` | 0 |
| `research/T22/probes/cutoff_kernel_closes.lean` | 0 |
| `research/T22/probes/cutoff_multiplier_closes.lean` | 0 |
| `research/T22/probes/cutoff_multiplier_field_closes.lean` | 0 |
| `research/T22/probes/orderzero_closes.lean` | 0 |
| `research/T22/probes/orderzero_isometry_closes.lean` | 0 |
| `research/T22/probes/restrict_bridge_closes.lean` | 0 |
| `research/T22/probes/rev383_negative.lean` | 1 |
| `research/T22/probes/rev383_nonvacuity.lean` | 0 |
| `research/T22/probes/rev386_mutation.lean` | 1 |
| `research/T22/probes/rev386_nonvacuity.lean` | 0 |
| `research/T22/probes/rev387_mutation_constant.lean` | 1 |
| `research/T22/probes/rev391_audit.lean` | 0 |
| `research/T22/probes/rev391_mutation.lean` | 1 |
| `research/T22/probes/rev393_audit.lean` | 0 |
| `research/T22/probes/rev393_mutation.lean` | 1 |
| `research/T22/probes/rev397_field_target.lean` | 1 |
| `research/T22/probes/rev397_field_target_406.lean` | 0 |
| `research/T22/probes/rev397_mutation.lean` | 1 |
| `research/T22/probes/rev397_nonvacuity.lean` | 0 |
| `research/T22/probes/rev406_mutation.lean` | 1 |
| `research/T22/probes/rev408_mutation.lean` | 1 |
| `research/T22/probes/rev409_mutation_constant.lean` | 1 |
| `research/T22/probes/rev409_nonvacuity.lean` | 0 |
| `research/T22/probes/rev418_negative.lean` | 1 |
| `research/T22/probes/rev423_negative.lean` | 1 |
| `research/T22/probes/weight_ratio_closes.lean` | 0 |
| `research/T22/probes/zero_ext_regularity_closes.lean` | 0 |
| `research/T22/probes/zero_extension_comparison_closes.lean` | 0 |
| `research/T24/axioms_ua2.lean` | 0 |
| `research/T24/axioms_ua3.lean` | 0 |
| `research/T24/axioms_ua4.lean` | 0 |
| `research/T24/axioms_ua5.lean` | 0 |
| `research/T24/axioms_ua6.lean` | 0 |
| `research/T24/axioms_ua7.lean` | 0 |
| `research/T24/axioms_ua8.lean` | 0 |
| `research/T24/axioms_ua9.lean` | 0 |
| `research/T24/axioms_ub1_ub3.lean` | 0 |
| `research/T24/axioms_ub4.lean` | 0 |
| `research/T24/axioms_ub5_ub6.lean` | 0 |
| `research/T24/axioms_ub7.lean` | 0 |
| `research/T24/axioms_uc1_ua1.lean` | 0 |
| `research/T24/axioms_uc2.lean` | 0 |
| `research/T24/axioms_uc3.lean` | 0 |
| `research/T24/probes/affine_divergence_closes.lean` | 0 |
| `research/T24/probes/affine_energy_closes.lean` | 0 |
| `research/T24/probes/affine_family_closes.lean` | 0 |
| `research/T24/probes/affine_force_closes.lean` | 0 |
| `research/T24/probes/affine_force_nonzero.lean` | 0 |
| `research/T24/probes/affine_momentum_closes.lean` | 0 |
| `research/T24/probes/affine_momentum_nonzero.lean` | 0 |
| `research/T24/probes/affine_nonisolated_closes.lean` | 0 |
| `research/T24/probes/affine_speed_closes.lean` | 0 |
| `research/T24/probes/assembled_closes.lean` | 0 |
| `research/T24/probes/multiple_api_on_canonical.lean` | 0 |
| `research/T24/probes/multiple_nonvacuity.lean` | 0 |
| `research/T24/probes/potential_pairing_closes.lean` | 0 |
| `research/T24/probes/regions_energy_closes.lean` | 0 |
| `research/T24/probes/rev392_nonvacuity.lean` | 0 |
| `research/T24/probes/rev392_widened_interval.lean` | 1 |
| `research/T24/probes/rev395_mutated_constant.lean` | 1 |
| `research/T24/probes/rev398_negative.lean` | 1 |
| `research/T24/probes/rev398_wrong_viscous_sign.lean` | 1 |
| `research/T24/probes/rev402_divergence_one.lean` | 1 |
| `research/T24/probes/rev403_negative_speed.lean` | 1 |
| `research/T24/probes/rev407_mutated_time.lean` | 1 |
| `research/T24/probes/rev414_mutation.lean` | 1 |
| `research/T24/probes/rev420_negative_interval.lean` | 1 |
| `research/T24/probes/rev430_mutation.lean` | 1 |
| `research/T24/probes/rev467_negative_eps_time.lean` | 1 |
| `research/T24/probes/rev467_nonvacuity.lean` | 0 |
| `research/T24/probes/rev468_mutation.lean` | 1 |
| `research/T24/probes/rev468_nonvacuity.lean` | 0 |
| `research/T24/probes/rev469_nonvacuity.lean` | 0 |
| `research/T24/probes/rev469_wrong_dissipation_constant.lean` | 1 |
| `research/T24/probes/rev471_wrong_dissipation_constant.lean` | 1 |
| `research/T24/probes/uc1_ua1_closes.lean` | 0 |

</details>

## 结论

167 个 Section 3 模块全部从清空后的产物目录重新 Built，退出码 0，Section 3 warning 1；全局日志有 108 条 warning。四个闸门均退出码 0，`make test` 输出 66 条标准公理检查行，合同注册检查报告 54。339 个 probe/axioms 文件中 298 个退出码 0，41 个已记录 reviewer negative/rejection probe 按预期退出码 1，非预期失败 0；公理扫描共 2106 组，其他公理名 0；源码 `sorry` grep 命中 16 处文档文字。

未全绿项目：

- `make check` 输出 `source_hashes_match: false`（命令退出码仍为 0）。
- Section 3 有 1 条 `defProp` warning，原文见上。
- Section 3 `sorry` grep 有 16 个文档文字命中，原文见上。
- 41 个 reviewer negative/rejection probe 按预期退出码 1；逐文件首个 error 行原文见上，不计为红项。

## 四段记录

**检查了什么：** Section 3 167 模块全量重编、四个闸门、339 个 probe/axioms 文件及公理扫描。

**树中现在有什么：** T10/T11/T12/T13/T14/T15/T16/T17/T18/T19/T20/T21/T22/T24 分别 7/30/12/7/1/18/4/15/12/7/13/11/12/18 个模块；167 个 `.olean`；54 个注册合同。

**什么不绿：** `make check` 的 `source_hashes_match: false`；Section 3 warning 1 条：

```text
warning: NSFormalization/Section3/T22/Assembly.lean:24:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
```

另有 16 个 `sorry` grep 文档文字命中及 41 个按预期退出码 1 的 reviewer negative/rejection probe；逐行原文见上，后者不计为红项。

**命令及结果：** `lake build` rc 0，148.47 s，167 Built、0 Replayed、0 error；全局 warning 108 条。`make check`/`make test`/`make test-mutations`/`check_contracts.py --base-ref main` 均 rc 0；`make test` 标准公理检查行 66；probe 扫描 298 通过、41 预期失败、0 非预期失败，其他公理名 0。
