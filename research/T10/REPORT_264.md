# Lane 264-SPEC-t10-draft-b report

## 1. 定了哪个合同

完成了 T10 “periodic data layer” 的双盲 Draft B。这条 lane 是规格工作，
没有证明新定理；它把第 3 节后续节点要用的对象和精确量词顺序定了下来：
周期 `H^s` 数据与物理场桥、均值/零均值分解、Leray 符号、压力规范、
`X_T`/`F_T`、经典解、最大存在时间、爆破集、相对稠密性和 `E_T` 范数。

## 2. Lean 里现在有什么

`research/T10/DraftB.lean` 是可 elaboration 的 statements-only 草案。物理层保留为
`R³` 上的单位周期函数，分析层使用 `lp (Fin 3 → ℤ) 2` 的三分量复系数数据，
并以 `A(-k)=conj(A(k))` 固定实场对称。权重是论文的
`(1+4π²|k|²)^(s/2)`；物理范数和力的 Bochner 范数都取数据上的
`ℝ≥0∞` 值下确界。`ClassicalSolutionT` 是新的合同结构，明确包含速度/压力周期性和
`∫_T³p=0`，不直接复用本地结构。`COMPARISON_B.md` 记录了论文到 Lean 的逐项对应、
所有表示选择、歧义和后续 lemma 清单。

## 3. 缺口是什么

本 lane 只固定合同，没有补分析证明。T11+ 仍需要 Parseval/单位立方体积分桥、
数据唯一性、Leray 投影在每个 `H^s` 上的良定义性和收缩性、零模与均值的对应、
压力规范化保持方程、谱隙/Poincaré、均值演化 `m'=̅f` 及零均值保持，以及
`ClassicalSolutionT` 与本地 periodic flow 结构的双向转换和往返引理。
这些都在 `COMPARISON_B.md` 的 “Needs a lemma” 中逐条列出。

## 4. 跑了什么

在仓库规定的 `verification` workspace 中运行：

```text
cd verification && lake env lean ../research/T10/DraftB.lean
```

结果：0 errors，0 warnings。草案只直接 import `Contracts.V1.Data` 和 Mathlib 的
`Analysis.Fourier/AddCircleMulti`，符合未来 `Contracts/V1/TorusData.lean` 的 import 边界。
