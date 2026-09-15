# REPORT 161 — A01 B1 时间正则阶梯，R1

## 1. 已证明哪些 theorem

**R1 完整闭合到 `m ≤ q + 1`，包括顶三阶和闭区间端点。**
命名空间 `NSFormalization.Section4.A01`；`RealVectorSobolev` 来自 Paper3，
`IsSobolevDatum` / `HasWeakDerivsL2Bound` 来自 D01；其余 open 与模块相同。
以下是五个 theorem 的原样签名：

```lean
theorem continuous_cylinder_word {q n : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 q)) (hn : n ≤ q) (w : Fin n → Fin 4) :
    Continuous (fun t => word 1 (u t) hn w)
```

```lean
theorem weakDerivsBound_word_top {q : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q), n + m ≤ q → ∀ (w : Fin n → Fin 4)
      (Z : EulerMeanSolenoidal.L2), ordinaryLift Z = word 1 u hn w →
      HasWeakDerivsL2Bound (⇑Z) (‖u‖ ^ 2) m
```

```lean
theorem weakDerivsBound_cylinder_top {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m ≤ q + 1) : HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) m
```

```lean
theorem datum_sub_norm_sq_le {q m : ℕ} (hm : m ≤ q + 1)
    (u v : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) v = v)
    (U V : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (hV : ordinaryLift V = value 1 v)
    (A B : RealVectorSobolev (m : ℝ))
    (hA : IsSobolevDatum (m : ℝ) (⇑U) A) (hB : IsSobolevDatum (m : ℝ) (⇑V) B) :
    ‖A - B‖ ^ 2 ≤ (4 : ℝ) ^ m * ‖u - v‖ ^ 2
```

```lean
theorem exists_continuous_datumPath {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (m : ℕ) (hm : m ≤ q + 1) :
    ∃ A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A
```

连续性是完整的 datum 路径连续性，不只是各时刻存在，也不只是范数连续。
关键增量界为 `‖A(t)-A(s)‖² ≤ 4^m · ‖u(t)-u(s)‖²`；开平方得常数 `2^m`。
无需经典解、光滑代表元、时间可导或 Duhamel 假设。Duhamel 的作用从 R2 开始。
所有 theorem 的公理恰好为 `[propext, Classical.choice, Quot.sound]`。

## 2. Lean 中现在有什么

- 新模块 [DatumPathContinuous.lean](../../formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean)：五个 theorem，未改既有模块。
- [axioms_b1_ladder.lean](axioms_b1_ladder.lean)：逐个 `#print axioms`，并在非空 `[0,1]` 上用 `u := 0`、`U := 0`，任意 `q` 的顶阶 `m := q+1` 实例化 R1。
- [B1_LADDER.md](B1_LADDER.md)：R1–R4 的精确目标、可复用树引理、接口限制及大小。
- [ATTEMPTS_B1_LADDER.md](ATTEMPTS_B1_LADDER.md)：全部失败尝试及原始错误。
- [gate_b1_build.log.gz](gate_b1_build.log.gz)、[gate_b1_check.log.gz](gate_b1_check.log.gz)：完整构建与 `make check` 输出；二者可 `gzip -cd` 阅读。

## 3. 缺口

| 阶梯 | 状态与大小 |
|---|---|
| R1 连续 datum 选择 | **DONE**，全部 `m ≤ q+1`，无三阶损失 |
| R2 Duhamel ⇒ datum 时间导数 | **L**；需要投影残差 datum 和 Banach 空间微积分恒等式，包含初始单侧导数 |
| R3 所有 `C^j_t H^m_x` | **L**；时间微分归纳、力的时间光滑性、所有阶在同一个 horizon 的兼容解 |
| R4 联合点值 C∞ | **L**；兼容代表元、混合偏导识别和全阶嵌入装配 |

不能循环使用 `A04.timeDeriv_isSobolevDatum`：它已假设 `ClassicalSolutionR` 和光滑 datum 路径。
`C01.residualPath` 也消费经典解，且其值需减压力梯度才是时间导数。
`D01.exists_smoothL2Field_of_memHInfty` 已假设代表元光滑。
仅有时间连续的 `F` 不足以得到任意次时间可导。
B2 的其他字段、跨阶共同解／先验界供给以及严格 `S < T` 的延拓余量仍独立存在。
本 checkout 未包含 brief 所述 `ConstructorPieces.lean`；没有访问别的工作树补取。

## 4. 命令与结果

所有 shell 首先 `. scripts/lean-env.sh`；所有 `lake` 命令均在 `verification/` 内执行。
四个门禁退出码均为 **0**。

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathContinuous
✔ [9984/9984] Built NSFormalization.Section4.A01.DatumPathContinuous (4.6s)
Build completed successfully (9984 jobs).
```

新模块没有 warning 或 error；Lake replay 了既有依赖 warning。完整原始输出见
`gate_b1_build.log.gz`，并未将依赖 warning 误报为零输出。

```text
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean
```

标准输出／错误输出合计 **0 字节**。

```text
$ cd verification && lake env lean ../research/A01/axioms_b1_ladder.lean
'NSFormalization.Section4.A01.continuous_cylinder_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.weakDerivsBound_word_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.weakDerivsBound_cylinder_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datum_sub_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_continuous_datumPath' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
$ make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 473,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
```

该步输出 26 个注册合同的完整闭包 JSON，原文随压缩日志保存（此处省略闭包数组）：

```text
  "registered_contracts": 26,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`source_hashes_match: false` 是检查器输出的仓库快照状态，检查器未因此失败；
已有 `BoundaryCorollary` 的 token 报告不是本模块的导入污染，逐 theorem 的 Lean 公理审计全部通过。
没有更新既有快照、合同、任务台账、NEXT_SESSION 或日志；遵守本 lane 只新增模块和 A01 records 的限制。

初次编译的两处 elaboration 错误和第二次的参数名错误均已修复，原文保存在 ATTEMPTS。
未使用超额心跳；未新增公理或占位证明；未 push、merge 或 rebase。
