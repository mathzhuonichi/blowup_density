# Section 3 集成分支全量编译检查（2026-09-18）

目的：验证当前集成批次（#339–#353 合入后）Section 3 全部模块可在同一源码树编译；只读检查。

## 环境

| 项 | 值 |
|---|---|
| 被检提交 | `d39f3a2d23dfe0017bcbf43a48a55977dbb7e7aa` |
| worktree | `.claude/worktrees/440-MAINT-section3-build-f` |
| 工具链 | Lean 4.34.0-rc2 (`6a10ac8c22be`) |
| 线程 | `LEAN_NUM_THREADS=6` |
| 运行方式 | `. scripts/lean-env.sh`；`lake` 从 `verification/` 执行 |

## Section 3 模块数与全量编译

`find formalization/NSFormalization/Section3 -name '*.lean' | sort` = **116 个模块**：

| 目录 | 模块数 |
|---|---|
| `Section3/T10/` | 7 |
| `Section3/T11/` | 30 |
| `Section3/T12/` | 12 |
| `Section3/T13/` | 7 |
| `Section3/T14/` | 1 |
| `Section3/T15/` | 6 |
| `Section3/T16/` | 4 |
| `Section3/T17/` | 8 |
| `Section3/T18/` | 6 |
| `Section3/T19/` | 1 |
| `Section3/T20/` | 9 |
| `Section3/T22/` | 12 |
| `Section3/T24/` | 13 |

删除 Section 3 的 `lib/lean` 与 `ir` 目录内编译产物后，以一条 `lake build` 命令重编全部 116 个模块，日志为 `tmp/section3_build.log`。

| 项 | 值 |
|---|---|
| 退出码 | **0** |
| 墙上时间 | **105.07 s** |
| error | **0** |
| Section 3 Built | **116 / 116** |
| Section 3 Replayed | **0** |
| warning 行 | **108** |
| `grep -c 'warning: NSFormalization/Section3/'` | **1** |
| `.olean` 落盘 | **116** |
| Section 3 `sorry` grep | **15**（均为文档文字） |

Section 3 warning 原文：

```text
warning: NSFormalization/Section3/T22/Assembly.lean:24:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
```

`sorry` grep 原文：

```text
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:46:No `sorry`, no `axiom`; every declaration prints `[propext, Classical.choice, Quot.sound]`.
formalization/NSFormalization/Section3/T22/OrderZero.lean:38:No `sorry`/`axiom`/`native_decide`; every declaration prints `[propext, Classical.choice,
formalization/NSFormalization/Section3/T22/CutoffDatum.lean:44:No `sorry`/`axiom`/`native_decide`; every declaration prints
formalization/NSFormalization/Section3/T15/HaarBridge.lean:42:`T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`.  No `sorry`, no named
formalization/NSFormalization/Section3/T11/PairingBound.lean:91:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T12/GradientLSix.lean:41:No `sorry`, no axiom, no `native_decide`, no named goal input; every declaration
formalization/NSFormalization/Section3/T12/CriticalL3Density.lean:50:No `sorry`, no axiom, no `native_decide`, no `maxHeartbeats` override, no named
formalization/NSFormalization/Section3/T12/HaarCube.lean:42:No `sorry`, no axiom, no `native_decide`, no named goal input.  Every
formalization/NSFormalization/Section3/T12/TameProduct.lean:59:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T20/H1Energy.lean:44:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
formalization/NSFormalization/Section3/T20/H1Trilinear.lean:76:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean:52:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
formalization/NSFormalization/Section3/T20/CriticalEnergy.lean:39:No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
```

执行命令：

```sh
. scripts/lean-env.sh
find formalization/.lake/build/lib/lean/NSFormalization/Section3 -type f -delete
find formalization/.lake/build/ir/NSFormalization/Section3 -type f -delete
find formalization/NSFormalization/Section3 -name '*.lean' | sort | sed -e 's#formalization/##' -e 's#\.lean$##' -e 's#/#.#g' > tmp/section3_modules.txt
cd verification
/usr/bin/time -f 'WALL_SECONDS=%e' -o ../tmp/section3_time.txt env LEAN_NUM_THREADS=6 lake build $(cat ../tmp/section3_modules.txt) > ../tmp/section3_build.log 2>&1
```

<details>
<summary>模块清单（116）</summary>

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
formalization/NSFormalization/Section3/T15/Bridges.lean
formalization/NSFormalization/Section3/T15/HaarBridge.lean
formalization/NSFormalization/Section3/T15/ParsevalZero.lean
formalization/NSFormalization/Section3/T15/Placement.lean
formalization/NSFormalization/Section3/T15/Scaling.lean
formalization/NSFormalization/Section3/T15/SingleCopy.lean
formalization/NSFormalization/Section3/T16/Assembly.lean
formalization/NSFormalization/Section3/T16/BallPotential.lean
formalization/NSFormalization/Section3/T16/LatticeLift.lean
formalization/NSFormalization/Section3/T16/LocalPotential.lean
formalization/NSFormalization/Section3/T17/Correction.lean
formalization/NSFormalization/Section3/T17/CorrectionDeriv.lean
formalization/NSFormalization/Section3/T17/CorrectionProfile.lean
formalization/NSFormalization/Section3/T17/ForceDeriv.lean
formalization/NSFormalization/Section3/T17/ForceProfile.lean
formalization/NSFormalization/Section3/T17/ForceSupport.lean
formalization/NSFormalization/Section3/T17/LatticeDeriv.lean
formalization/NSFormalization/Section3/T17/Transport.lean
formalization/NSFormalization/Section3/T18/CrossTransport.lean
formalization/NSFormalization/Section3/T18/Divergence.lean
formalization/NSFormalization/Section3/T18/ForceClass.lean
formalization/NSFormalization/Section3/T18/Insertion.lean
formalization/NSFormalization/Section3/T18/Kinematics.lean
formalization/NSFormalization/Section3/T18/Momentum.lean
formalization/NSFormalization/Section3/T19/Bookkeeping.lean
formalization/NSFormalization/Section3/T20/BIntegral.lean
formalization/NSFormalization/Section3/T20/ConstantTransport.lean
formalization/NSFormalization/Section3/T20/CriticalEnergy.lean
formalization/NSFormalization/Section3/T20/CriticalRegularity.lean
formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean
formalization/NSFormalization/Section3/T20/H1Energy.lean
formalization/NSFormalization/Section3/T20/H1Trilinear.lean
formalization/NSFormalization/Section3/T20/MeanReduction.lean
formalization/NSFormalization/Section3/T20/YBound.lean
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
formalization/NSFormalization/Section3/T24/PotentialPairing.lean
```

</details>

## 闸门

| 命令 | 退出码 | 结果 |
|---|---:|---|
| `make check` | 0 | `check_work_queue`: 45 work items consistent；13 policy tests OK；`source_hashes_match: false`；本次无 `--base-ref` 时 `base_compatibility_checked: false` |
| `make test` | 0 | **50** lines `checked; standard logical axioms only`（46 个注册合同） |
| `make test-mutations` | 0 | implementation_refactor accepted；其余三项 rejected as required |
| `python3 experiments/check_contracts.py --base-ref main` | 0 | `registered_contracts: 46`; `base_compatibility_checked: true` |

四个闸门墙上时间分别为 9.99 s、2.08 s、12.24 s、4.88 s。`make test` 的 50 行来自测试模块中检查的声明行数；注册合同数由 `check_contracts.py` 报告为 46。

## Probe 与公理审计扫描

扫描集合为每个 `research/T1*/**/*_closes.lean`、`research/T1*/axioms_*.lean`、`research/T1*/probes/api_on_canonical.lean`，以及 `research/T11/probes/assembly_closes.lean`，去重后共 **148** 个文件。以 4 路并行、每个 `LEAN_NUM_THREADS=2` 执行 `cd verification && lake env lean ../<file>`：

| 项 | 值 |
|---|---:|
| 通过 | **148 / 148** |
| 失败 | **0** |
| 首个 error 行 | 无 |
| 公理结果 | `[propext, Classical.choice, Quot.sound]`（895 组；不同列表 0） |
| 其他公理名 | **0** |

公理扫描合并了跨行的 `depends on axioms: [...]`，逐名与三个标准公理比较；结果保存在 `tmp/axiom_scan_f.json`。

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
| `research/T15/axioms_u2.lean` | 0 |
| `research/T15/axioms_u3.lean` | 0 |
| `research/T15/axioms_ucan.lean` | 0 |
| `research/T15/axioms_utb1.lean` | 0 |
| `research/T15/axioms_utb2.lean` | 0 |
| `research/T15/probes/api_on_canonical.lean` | 0 |
| `research/T15/probes/haar_bridge_closes.lean` | 0 |
| `research/T15/probes/parseval_zero_closes.lean` | 0 |
| `research/T15/probes/placement_closes.lean` | 0 |
| `research/T15/probes/single_copy_closes.lean` | 0 |
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
| `research/T17/axioms_u7.lean` | 0 |
| `research/T17/axioms_ucan.lean` | 0 |
| `research/T17/probes/correction_profile_closes.lean` | 0 |
| `research/T17/probes/derivative_bounds_closes.lean` | 0 |
| `research/T17/probes/force_profile_closes.lean` | 0 |
| `research/T17/probes/force_support_closes.lean` | 0 |
| `research/T17/probes/lattice_deriv_closes.lean` | 0 |
| `research/T17/probes/transport_closes.lean` | 0 |
| `research/T18/axioms_u1.lean` | 0 |
| `research/T18/axioms_u2_u4.lean` | 0 |
| `research/T18/axioms_u5_u6.lean` | 0 |
| `research/T18/probes/insertion_closes.lean` | 0 |
| `research/T18/probes/u2_u4_closes.lean` | 0 |
| `research/T18/probes/u5_u6_closes.lean` | 0 |
| `research/T19/axioms_u1_6.lean` | 0 |
| `research/T19/probes/bookkeeping_closes.lean` | 0 |

</details>

## 结论

116 个 Section 3 模块全部从清空后的产物目录重新 Built，退出码 0，Section 3 warning 1；全局日志有 108 条 warning。四个闸门均退出码 0，`make test` 输出 50 条标准公理检查行，合同注册检查报告 46。148/148 个 probe/axioms 文件通过；公理扫描共 895 组，其他公理名 0；源码 `sorry` grep 命中 15 处文档文字。

未全绿项目：

- `make check` 输出 `source_hashes_match: false`（命令退出码仍为 0）。
- Section 3 有 1 条 `defProp` warning，原文见上。
- Section 3 `sorry` grep 有 15 个文档文字命中，原文见上。

## 四段记录

**检查了什么：** Section 3 116 模块全量重编、四个闸门、148 个 probe/axioms 文件及公理扫描。

**树中现在有什么：** T10/T11/T12/T13/T14/T15/T16/T17/T18/T19/T20/T22/T24 分别 7/30/12/7/1/6/4/8/6/1/9/12/13 个模块；116 个 `.olean`；46 个注册合同。

**什么不绿：** `make check` 的 `source_hashes_match: false`；Section 3 warning 1 条：

```text
warning: NSFormalization/Section3/T22/Assembly.lean:24:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
```

另有 15 个 `sorry` grep 文档文字命中，逐行原文见上。

**命令及结果：** `lake build` rc 0，105.07 s，116 Built、0 Replayed、0 error；全局 warning 108 条。`make check`/`make test`/`make test-mutations`/`check_contracts.py --base-ref main` 均 rc 0；`make test` 标准公理检查行 50；probe 扫描 148/148 通过，其他公理名 0。
