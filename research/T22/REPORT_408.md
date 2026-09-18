# Lane 408 — T22 U-B2

## 1. 证明的定理（精确陈述）

命名空间 `NSFormalization.Section3.T22`；`Space` 是三维实 EuclideanSpace，
`SpatialField = Space → Space`，datum 与 jets 使用 D01 的 canonical 定义。
以下为新模块的全部定理签名：

```lean
theorem contDiff_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (_hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    ContDiff ℝ ∞ (zeroExtension Ω z)

theorem hasCompactSupport_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (_hΩ : IsOpen Ω) (_hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (_hKΩ : K ⊆ Ω)
    (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    HasCompactSupport (zeroExtension Ω z)

theorem memLp_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    MemLp (zeroExtension Ω z) 2 volume

theorem smoothJets_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    SmoothSquareIntegrableJets (zeroExtension Ω z)

theorem exists_datum_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) (s : ℝ) :
    ∃ A, IsSobolevDatum s (zeroExtension Ω z) A
```

证明在 Ω 内使用与 z 的邻域相等，在 Ω 外使用与零场的邻域相等。
紧支撑传给每阶 Fréchet 导数，连续紧支撑推出 L²，再调用
`D01.exists_isSobolevDatum_of_contDiff_memLp`，覆盖任意实数阶 s。
五个主定理均精确依赖 `[propext, Classical.choice, Quot.sound]`。

## 2. 文件

- `formalization/NSFormalization/Section3/T22/ZeroExtRegularity.lean`：五个定理；恢复的证明原样通过。
- `research/T22/probes/zero_ext_regularity_closes.lean`：内半径 1/4、外半径 1/2 的 `ContDiffBump` 乘第一个单位基向量；Ω = ball 0 1，K = closedBall 0 (1/2)。验证支撑、零延拓在原点非零，以及全部五个结论。
- `research/T22/axioms_ub2.lean`：五个主定理的公理审计。
- `research/T22/ATTEMPTS_UB2.md`：证明路线和修正记录。
- `research/T22/T22_SPLIT.md`：U-B2 状态更新。
- `research/T22/REPORT_408.md`：本报告。

仅新增 Lean 模块；未修改任何既有 Lean 模块。按本 lane 的明确范围，
共享 NEXT_SESSION/LESSONS 未改，续接记录保存在本报告和 ATTEMPTS。

## 3. 缺口与错误

U-B2 无剩余缺口，无 named input，无占位证明，无 heartbeat 上调。
续接新增探针时出现并已修复：
`Invalid field ne_zero: The environment does not contain OrthonormalBasis.ne_zero`。
修复为 `OrthonormalBasis.toBasis.ne_zero`。历史紧支撑构造器参数误用见 ATTEMPTS。
构建会 replay 既有依赖的 linter/deprecation 警告；新模块直接检查零输出。

## 4. 命令与结果

所有 Lean 命令先 `. scripts/lean-env.sh`，在 `verification/` 中运行，
环境 `LEAN_NUM_THREADS=6`。

- `lake build NSFormalization.Section3.T22.ZeroExtRegularity`：退出 0，9879 jobs，0 errors。
- `lake env lean ../formalization/NSFormalization/Section3/T22/ZeroExtRegularity.lean`：退出 0，零输出。
- `lake env lean ../research/T22/probes/zero_ext_regularity_closes.lean`：退出 0，零输出。
- `lake env lean ../research/T22/axioms_ub2.lean`：退出 0，五个定理均精确打印标准三公理。
- 根目录 `make check`：退出 0，13 policy tests OK，45 work items 一致。
- `lake test`（从 verification 运行，等价 Makefile 的 test target）：退出 0，合同测试通过。
- 根目录 `make test-mutations`：退出 0；implementation_refactor accepted，admitted_proof / extra_axiom / weakened_hypothesis 按预期拒绝。
- `git diff --check`：退出 0。

交付提交位于 `erenup/408-T22-UB2-zero-ext-regularity`；未 push、merge 或 rebase。
