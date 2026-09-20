# 270-SPEC-t12-draft-b 报告

## 1. 证了哪个定理

本 lane 是双盲陈述草案，没有提供证明。`DraftB.lean` 精确声明了 T12
的七个目标不等式：周期 `eq:Rproduct`、`H² → L∞`、均值零
`Ḣ¹⁄² → L³`、合并的 `‖∇v‖₃ + ‖Λv‖₃`、`‖∇v‖₆ ≤ C‖Δv‖₂`、
`‖v‖_{H²} ≤ C‖Δv‖₂` 和谱隙。临界齐次范数按论文只对均值零场定义；
`eq:Rproduct` 和 `H² → L∞` 没有被错误加上均值零假设。

## 2. Lean 里现在有什么

- `research/T12/DraftB.lean` 可独立 elaboration；物理层是 `R³` 上单位周期场，
  系数层是以 `(1+4π²|k|²)^(s/2)` 或 `|2πk|^s` 加权的
  `lp (Fin 3 → ℤ) 2`。向量分量用 `WithLp 2` 组装。
- 草案定义了非齐次/齐次 datum 及 `ENNReal` 范数、`k=0` 系数形式的
  均值零子空间、物理 `meanZeroPart`、梯度、Laplacian 和 `Lambda` 乘子见证。
- `MeanZeroSobolevAPI K : Prop` 恰有七个不等式字段。由于 Lean 不允许从
  `Prop` 结构投影 `ℝ` 数据，所有先于场选定的实常数及其正性放在
  `MeanZeroSobolevConstants` 中，API 以它为参数。
- `research/T12/COMPARISON_B.md` 给出论文子句对照表、选择、歧义、缺失引理和
  A03/A05 的 Section 4 对应合同。

## 3. 缺口是什么

这些本地定义需与 T10 最终数据层对齐并加 `rfl`/类型化桥。证明上的核心缺口是
对任意频谱截断一致的均值零 `Ḣ¹⁄²(T³) → L³(T³)`；现有
`PeriodicFiniteCriticalInterface`/`PeriodicCriticalBridge` 保留有限模的基数或逆权损失，
不能代替它。其余需要 Parseval/重建、卷积 tame 估计、微分与乘子的 Fourier
恒等式、谱隙、Hessian--Laplacian 恒等式和物理 torus lift 的可测性/范数桥。

## 4. 跑了什么命令、什么结果

- `cd verification && lake env lean ../research/T12/DraftB.lean`：通过，无警告。
- 对所用 Mathlib 名称运行了 `#check`：`UnitAddTorus`、
  `UnitAddTorus.measurableEquivPiIoc`、`UnitAddTorus.mFourierCoeff`、`lp`、
  `WithLp`、`WithLp.toLp`、`eLpNorm`、`MemLp`、`ContDiff`、`UnitPeriods`
  全部通过。
- `git diff --check`：通过。
- `rg` 检查 `DraftB.lean` 中的 `sorry/admit/axiom/native_decide`：无匹配。
- `make check`：通过。输出仍列出基线已知的
  `Paper1/BoundaryCorollary.lean:90` `sorry` 和 `source_hashes_match: false`，但检查器返回成功，
  本 lane 未修改该源文件。
- `make test`：通过；仅有已有上游 linter 警告。
- `make test-mutations`：通过；四类 mutation 结果均符合预期。
- 双盲审计注：为查找 Lean `Prop` API 的库内先例时，一次过宽的 `rg`
  意外返回了 `research/T13/RECONCILIATION.md` 的一行搜索结果，仅含与 T12
  无关的 localization API 字段名。未打开该文件，也未在本草案中使用该信息。
