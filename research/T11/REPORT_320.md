# 320-T11 — ClassicalAssembly（部分交付；U9d2 未闭合）

## 1. 定理与精确陈述

本次证明全阶 persistence 的空间恢复、完整无散字段和连续 Sobolev 路径字段。
`classicalSolutionT_projected` 只消费一个已经存在的经典解，不制造经典解。
唯一具名输入为 U9d1 的结论，参数只保留结论实际依赖的 `T,u`：

```lean
def PersistenceInput (T : ℝ) (u : ℝ → PeriodicSobolev 3) : Prop :=
  ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn u_m (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, ∀ i k,
        torusPhysicalCoeff (m : ℝ) (u_m t) i k = torusPhysicalCoeff 3 (u t) i k
```

`torusPhysicalCoeff s A i k = W(k)^(-s/2) * A.1 i k`。
`physicalCoeff_eq_iff_reweight` 证明此系数相等恰等于规范 `IsPeriodicReweight`；
没有把 phantom index 的载体相等当成 Sobolev 阶数提升。
`persistence_of_classicalSolutionT` 证明任意具有指定 H³ 路径的经典解都满足该输入。

主要已证签名如下（原文取自新模块）：

```lean
theorem persistence_physical_sobolev {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) :
    ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ torusPhysicalVelocity u (t, x)) (G t)
```

```lean
theorem persistence_physical_spatial_smooth {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) {t : ℝ} (ht : t ∈ Ico 0 T) :
    ContDiff ℝ ∞ (fun x ↦ torusPhysicalVelocity u (t, x))
```

```lean
theorem assembly_mild_solenoidal {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hA : IsSolenoidalPeriodicDatum A)
    (hP : ∀ t : ℝ, 0 ≤ t → IsSolenoidalPeriodicDatum (P t))
    (hu : TorusForcedMildOn C A P T u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsSolenoidalPeriodicDatum (u t)
```

```lean
theorem persistence_mild_physical_divergence {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {a : SpatialField} {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (ha : a ∈ initialClassT) (hA : IsPeriodicDatum 3 a A)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (hp : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence (torusPhysicalVelocity u) t x = 0
```

```lean
theorem classicalSolutionT_projected {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
        (f (t, x) - convectionDivergenceT w.velocity t x) -
          pressureGradient w.pressure t x
```

空间证明：第 `2*N+3` 阶的真实重加权给出 `W^N |û|` 绝对可求和；
Fourier character 的 n 阶导数有统一界 `‖phase(k)‖^n ≤ (3 W(k))^n`；
Mathlib `contDiff_tsum` 给出每个空间切片 C∞。
无散证明：固定 Fourier 模的散度是连续实线性泛函，故与实际可积的
Duhamel 积分交换；热演化及投影对流保持其核。Fourier 反演再给出物理无散性。
包括 `t=0`，没有缩短 horizon。

`classicalAssembly_nonzero` 在同一 `T=1` 上同时检验实际强迫 mild 方程、
PersistenceInput、完整经典恢复和局部正则性；初值与外力均为 `coordinateVector 0`，
速度为 `(1+t) • coordinateVector 0`，两者非零。该实例不证明任意数据目标。

## 2. 文件

新增：

- `formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean`
- `research/T11/probes/classical_assembly_closes.lean`
- `research/T11/axioms_classical_assembly.lean`
- `research/T11/ATTEMPTS_CLASSICAL_ASSEMBLY.md`
- `research/T11/REPORT_320.md`

仅追加记录：`T11_SPLIT.md` §1、`EXISTENCE_ROUTE.md` 的 U9d2 状态。
已有 Lean 模块、合同、NEXT_SESSION 和生成台账不改；本报告承担交接。
公理审计守卫所有 26 个具名声明（含两个具名局部实例），每项精确为
`[propext, Classical.choice, Quot.sound]`。新模块无 warning。

## 3. 缺口与错误

**一般 U9d2 目标没有证明，未达到完整目标或单一进一步 peeling 输入后的条件闭合标准。**
未引入把剩余目标全部重述的假设。除 PersistenceInput 外，没有新增具名分析输入。
尚缺：Duhamel 时间微分及所有阶路径的时间光滑性、包括初始边界的联合 C∞、
一般物理压力构造及 pressure_gradient / pressure_smooth / pressure_gauge /
pressure_periodic / pressure_poisson、动量方程及最终结构装配。
`classicalSolutionT_projected` 解决的是已有经典解的冗余字段，不能据此声称 mild → PDE 已证。

原始完整目标仍原样为：

```lean
∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
  (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
  a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
  ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
    IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
    (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
    TorusForcedMildOn C A P T u →
    ∃ w : ClassicalSolutionT ν a g T,
      PeriodicLocalRegularity ν a g T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u
```

本 lane 获准在 mild 解上加入 PersistenceInput 作为 U9d1 输出；即使加入它，
上述完整存在性结论在本次交付中仍未闭合。probe 文件头明确说明它只检查所列部件
和常量族；文件名中的 closes 不是一般目标完成声明。

实际调试错误（均已修复）：

```text
Unknown constant `ContinuousLinearMap.norm_smulRight_le`
(deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
unexpected token 'set_option'; expected 'lemma'
failed to synthesize instance of type class LE Type
The target expression is not type-correct under the `implicit` transparency level
```

未闭合的分析步骤并非编译器报错，不以这些已修复报错误称目标不可证。
详情和准确输入见 ATTEMPTS_CLASSICAL_ASSEMBLY.md。

## 4. 命令与结果

每次 Lean 命令先 `. scripts/lean-env.sh`；lake 均从 `verification/` 运行，
`LEAN_NUM_THREADS=6`。原始日志在工作树内 `tmp/320/`。

| 命令 | 结果 |
|---|---|
| `lake build NSFormalization.Section3.T11.ClassicalAssembly` | exit 0 |
| `lake env lean ../formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean` | exit 0，无输出 |
| `lake env lean ../research/T11/probes/classical_assembly_closes.lean` | exit 0，部分字段及非零实例 |
| `lake env lean ../research/T11/axioms_classical_assembly.lean` | exit 0，26 个精确公理守卫 |
| 根目录 `make check` | exit 0 |
| 根目录 `make test` | exit 0，既有合同测试通过 |
| 根目录 `make test-mutations` | exit 0，4 类变异符合预期 |

提交消息 `[320-T11] ClassicalAssembly`；未 push、merge 或 rebase。
门禁通过不改变本 lane 未完成一般目标的状态。
