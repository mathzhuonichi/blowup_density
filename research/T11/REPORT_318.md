# 318-T11 / U9d — PhysicalRecovery（部分交付，U9d 未闭合）

## 1. 定理与精确陈述

所有新结果均无具名分析输入。构造的是实际 Fourier 级数，不是 L² 等价类的任意代表。
完整签名见模块；主要结果为：

```lean
theorem torusPhysicalField_datum (A : PeriodicSobolev 3) :
    IsPeriodicDatum 3 (torusPhysicalField A) A

theorem torusPhysicalField_eq {a : SpatialField} {A : PeriodicSobolev 3}
    (ha : Continuous a) (hA : IsPeriodicDatum 3 a A) :
    torusPhysicalField A = a

theorem torusPhysicalVelocity_datum (u : ℝ → PeriodicSobolev 3) (I : Set ℝ) :
    IsPeriodicSobolevPathOn 3 I (torusPhysicalVelocity u) u

theorem torusPhysicalVelocity_initial {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {a : SpatialField} {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (ha : a ∈ initialClassT) (hA : IsPeriodicDatum 3 a A)
    (hu : TorusForcedMildOn C A P T u) (x : Space) :
    torusPhysicalVelocity u (0, x) = a x

theorem torusForcedMildOn_physical_continuous {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A P T u) :
    ContinuousOn (torusPhysicalVelocity u) (Icc (0 : ℝ) T ×ˢ (univ : Set Space))

theorem torusPhysicalField_datum_reweight {s : ℝ} {A : PeriodicSobolev 3}
    {B : PeriodicSobolev s} (hB : IsPeriodicReweight 3 s A B) :
    IsPeriodicDatum s (torusPhysicalField A) B
```

还证明系数绝对可求和、共轭对称、复反演和实场一致、全局空间周期、
H³→连续环面分量的实 CLM、统一范数界、系数与空间点的联合连续性、
精确 reweight 路径传递、给定 H³ 路径时间光滑性时的物理分量时间光滑性。
没有把 H³ 路径的时间光滑性当作 mild 解的已证性质。

非空检验实际调用 lane 317 的无条件合同和强迫 Picard 定理，初值、力均非零。
另有任意正 T 的完整常量空间模式检验：

```lean
theorem torusForcedMildOn_affine_constant {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    (c : Space) (hT : 0 ≤ T) :
    TorusForcedMildOn C (torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c) T
      (fun t ↦ (1+t) • torusConstantDatum 3 c)

theorem torusPhysicalRecovery_affine_constant (ν T : ℝ) (c : Space) (hT : 0 < T) :
    ∃ w : ClassicalSolutionT ν (fun _ ↦ c) (fun _ ↦ c) T,
      PeriodicLocalRegularity ν (fun _ ↦ c) (fun _ ↦ c) T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity
        (fun t ↦ (1+t) • torusConstantDatum 3 c)
```

这两条的 horizon 是同一个给定 T；取 `c = coordinateVector 0` 得到非零速度和力。
这只是检验实例，不是一般数据定理。

## 2. 文件

新增：

- `formalization/NSFormalization/Section3/T11/PhysicalRecovery.lean`
- `research/T11/probes/physical_recovery_closes.lean`
- `research/T11/axioms_physical_recovery.lean`
- `research/T11/ATTEMPTS_PHYSICAL_RECOVERY.md`
- `research/T11/REPORT_318.md`

仅追加：`T11_SPLIT.md` §1 状态行、`EXISTENCE_ROUTE.md` 的 U9d 状态。
已有 Lean 模块、合同、生成台账、NEXT_SESSION.md 均未修改。
交接由本报告承担。未 push、merge 或 rebase。

公理文件逐项守卫 **42 个具名声明**（含两个明确命名的局部实例），
输出精确为 `[propext, Classical.choice, Quot.sound]`。
没有禁用项、全局 heartbeat 修改或新占位输入。

## 3. 缺口与错误

**一般 U9d 目标未证明；用户指定的完整 (ii)+(iii) 后备交付也未达到。**
没有把以下完整目标重述成具名假设，没有声称条件闭合。它仍原样为：

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

仍缺共同 horizon 的全阶 bootstrap、一般物理速度联合光滑性及无散性、
一般物理压力及 Poisson/gauge/gradient、Duhamel 时间微分与动量/投影方程。
因此没有残余具名输入可供后续 lane 直接偿还；这份是无条件基础部件交付，
不满足“单一 peeling 输入后证明完整目标”的完成标准。

路线上的具体难点：H^m 对流项在 H^(m−1)，直接用热核升至 H^(m+1)
需要两阶导数，朴素时间控制为 `(t-s)^(-1)`，不可积。
现有一阶 integrable smoothing 不能独自完成该整阶提升；需分数阶、
时间抵消或高阶 persistence 的进一步论证。这不说明目标本身为假。

实际调试错误包括：

```text
Invalid field `re`: The environment does not contain `Continuous.re`
failed to synthesize instance of type class
  FiniteDimensional ℝ C(UnitAddTorus (Fin 3), ℂ)
... has type ... ^ (2 : ℕ) but is expected to have type ... ^ (2 : ℝ)
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
The target expression is not type-correct under the `implicit` transparency level
```

这些编译错误已修复，方法详见 attempts。一般分析缺口不是虚构的编译报错。
probe 的指定文件名不代表完整目标闭合；文件头显式说明它只检查本次子结果。

## 4. 命令与结果

每条 Lean 命令先 `. scripts/lean-env.sh`，`lake` 均从 `verification/`
运行并设 `LEAN_NUM_THREADS=6`。执行的检查如下：

| 命令 | 结果 |
|---|---|
| `lake build NSFormalization.Section3.T11.PhysicalRecovery` | exit 0 |
| `lake env lean ../formalization/NSFormalization/Section3/T11/PhysicalRecovery.lean` | exit 0；新模块无输出 |
| `lake env lean ../research/T11/probes/physical_recovery_closes.lean` | exit 0；仅子结果/常量族探针 |
| `lake env lean ../research/T11/axioms_physical_recovery.lean` | exit 0；42 项精确公理守卫 |
| 根目录 `make check` | exit 0 |
| 根目录 `make test` | exit 0；既有合同测试通过 |
| 根目录 `make test-mutations` | exit 0；4 类变异按预期 |

依赖重放含已有 warning；新模块无 warning。原始日志在工作树内
`tmp/318/`，不把上万行门禁输出提交到报告。

提交消息：`[318-T11] PhysicalRecovery`。门禁通过只说明交付部件经过检查，
不改变 U9d 未完成的状态。
