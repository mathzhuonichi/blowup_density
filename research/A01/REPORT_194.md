# REPORT 194 — P4a complement path

## 1. 定理、精确陈述与命名输入

`NSFormalization.Section4.A01.exists_complement_paths` 与
`NSFormalization.Section4.A01.exists_complement_joint_representative` 导出到 A01
命名空间；定义及辅助引理位于 `A01.ComplementPath`。

共用参数如下（逐字来自模块；没有压力或时间导数输入）：

```lean
variable {f : A02.SpaceTimeField} {ν S : ℝ}
variable (hf : MemForceR f) (hν : 0 < ν) (hS : 0 < S)
-- `a` is the standard smooth square-integrable initial velocity.
variable (a : SmoothL2Field Space)
-- `U` is the ordinary L² velocity path restricted to the common closed horizon.
variable (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
-- `hpairs` is precisely the all-order cylinder-pair conjunction exported by lane 192:
-- ordinary realization, divergence freedom, angular invariance, and the forced mild equation.
variable (hpairs : ∀ q (hq : 6 ≤ q),
  ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
    (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
    (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
    (∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
    ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq
        (sobolevPath (C01.forcePath (S := S) hf)
          (C01.forcePath_jetLp_continuous (S := S) hf) q))
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t)

```

`hf` 是标准光滑外力类的限制；`hν`、`hS` 是正黏度、正视界限制。
`a` 是标准光滑 L² 初值，`U` 是同一速度的闭区间 L² 路径。
`hpairs` 是 192 导出的逐阶共同载体 cylinder-pair 合取；192 同时导出的
初值等式与速度 datum-path 合取不必另作输入。本模块从 cylinder-pair
和标准外力重新导出所需的残差 datum 路径。所有输入对非零局部光滑解
仍是标准性质的限制，没有要求双侧端点时间导数。

令 `R := residualCarrier hf hν hS a U hpairs`，它从 q=7 的固定速度
载体在 k=6 形成 **未投影** 残差后下降至普通 L²。
`residualDatum … t := orderZeroDatumCLM (R t)`。
`physicalComplement … t` 是该零阶 datum 的 Leray 余项的物理 L² 重建，
时间区间之外仅用 `projIcc` 定义其值。

```lean
theorem exists_complement_paths :
    ∃ w : ℝ → (Space → Space),
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (G t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0 (⇑(residualCarrier hf hν hS a U hpairs t)) A ∧
        IsSobolevDatum 0 (w t.1) (lerayComplement 0 A)

theorem exists_complement_joint_representative :
    ∃ G : A02.SpaceTimeField,
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      ∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume]
        physicalComplement hf hν hS a U hpairs t.1
```

物理桥不涉及时间微分：任何光滑空间代表元 `z =ᵐ U t` 都有
`R t =ᵐ νΔz + f(t,·) − Dz·z`，并且同一个零阶 datum 表示该残差。
供 195 直接使用的标准速度场记法为：

```lean
theorem residualDatum_physicalSlice (velocity : A02.SpaceTimeField)
    (t : Icc (0 : ℝ) S)
    (hz : ContDiff ℝ ∞ (fun x => velocity (t.1, x)))
    (hzu : (fun x => velocity (t.1, x)) =ᵐ[volume] ⇑(U t)) :
    IsSobolevDatum 0
      (fun x => ν • NavierStokes.ProblemStatement.spatialLaplacian velocity t.1 x +
        (f (t.1, x) - NavierStokes.ProblemStatement.advection velocity t.1 x))
      (residualDatum hf hν hS a U hpairs t)
```

相关精确 a.e. 版本：

```lean
theorem residualCarrier_physical (t : Icc (0 : ℝ) S) (z : Space → Space)
    (hz : ContDiff ℝ ∞ z) (hzu : z =ᵐ[volume] ⇑(U t)) :
    (⇑(residualCarrier hf hν hS a U hpairs t)) =ᵐ[volume]
      (fun x => ν • sliceLaplacian z x + (f (t.1, x) - fderiv ℝ z x (z x)))
```

有限阶证明真实损失 `k + 2 + 2*j ≤ q+1`，取 `k=max 6 m` 后降低阶数。
余项的各阶相容性使用 `lerayComplement_lowerVectorL`。
190 的 L² 类型没有无散限制，因此直接使用其 generic joint representative
定理；所得切片恒等式包括 `t=S`，光滑性在要求的 `Ico 0 S ×ˢ univ` 上。

## 2. 文件

- `formalization/NSFormalization/Section4/A01/ComplementPath.lean`：38 个新声明，
  加两个 A01 命名空间导出别名；没有修改已有 Lean 模块。
- `research/A01/axioms_complement_path.lean`：逐声明公理审计，以及真实零力 /
  零 cylinder-pair 在 `[0,1]` 上对主存在性定理的非空洞实例。
- `research/A01/ATTEMPTS_COMPLEMENT_PATH.md`：路线、失败诊断与解决办法。
- `research/A01/A3_SPLIT.md`：新增 “P4a complement path” 行。
- 本报告 `research/A01/REPORT_194.md`。

189 的未投影残差公式与有限阶光滑性证明已复制、注明出处并放入独立
namespace；没有 import 189 分支，也没有 push、merge 或 rebase。

## 3. 缺口与错误原文

数学交付无未闭合缺口；没有新增分析假设。压力势、投影动量对接由后续
195/189 负责，本模块不声称完成那些任务。

开发过程中出现且已解决的错误包括：
`failed to synthesize T2Space (RealVectorSobolev 0)`；
`(deterministic) timeout at isDefEq, maximum number of heartbeats (400000)`；
`object file ... Euler/SmoothL2Series.olean ... does not exist`。
解决过程详见 ATTEMPTS。

普通 `lake build` 成功，但重放依赖模块已有 warnings（例如
`FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'`）。
本模块单独 `lake env lean` 为 0 输出。另以 Lake 的
`-q --log-level=error` 执行静默成功检查；不改动任何依赖或其 warning 设置。

## 4. 命令与结果

每个 Lean shell 均先 `. scripts/lean-env.sh`，所有 lake 从 `verification/`
执行，`LEAN_NUM_THREADS=6`。以下检查均成功：

```sh
lake build NSFormalization.Section4.A01.ComplementPath
lake -q --log-level=error build NSFormalization.Section4.A01.ComplementPath
lake env lean ../formalization/NSFormalization/Section4/A01/ComplementPath.lean
lake env lean ../research/A01/axioms_complement_path.lean
lake test
```

根目录：`make check`、`python3 experiments/test_contract_mutations.py`、
`git diff --check` 均成功。依赖补编：
`lake build Euler.SmoothL2Series NSFormalization.Section4.A04.ZeroSolution`。

38 个声明及两个导出名的传递公理均恰为
`[propext, Classical.choice, Quot.sound]`。非空洞零实例通过。
模块没有 `sorry`、`admit`、`axiom` 或 `native_decide`。
