# 271-SPEC-t16-draft-a 报告

## 1. 证了哪个定理

本 lane 不提交证明，而是完成了 `03-torus.tex:176-216` 的
`lem:potential` 双盲陈述草案 A。陈述覆盖径向向量势及
`curl A = v`、两类光滑 Urysohn 截断、`w_ε` 的局部公式、全局光滑性、
空间周期性、无散性、时空支撑，以及活跃区间
`[T-ε²,T)` 上的 `eq:bgzero` 开邻域消去。

## 2. Lean 里现在有什么

`DraftA.lean` 中有 `Prop` 值结构
`LocalDivergenceFreeCutoffAPI` 和带完整输入/见证量词次序的
`localDivergenceFreeCutoffStatement`。由于 Lean 不允许从 `Prop` 结构投影
数据，`θ`、`η`、`ε₀`、`A`、`w_ε` 等作为结构参数，由外层命题显式存在量化；
结构字段本身全部是论文的具体性质，没有占位 `Prop`。

物理层使用 `ℝ³` 上的单位周期场。周期场不可能同时是非零且在整个
`ℝ³` 紧支，因此支撑写成一个坐标球的整数平移并；原始
`eq:cutoff` 公式只在所选坐标球中陈述，再由独立的周期性和支撑字段描述
全局延拓。与 I02 重合的对象沿用了同名字段。文件还逐项标出了等待 T10
注册/对齐的 `lp (Fin 3 → ℤ) 2` 数据、非齐次/齐次权、总化范数、零模条件
和均值零分解。

`COMPARISON_A.md` 给出了逐条 paper-to-Lean 对照、表示选择、歧义、待证
引理，以及 Section 4 I02 的 V1/V2 合同和 binding 对应关系。

## 3. 缺口是什么

这仍是研究草案，尚未注册为版本化合同，也没有 binding 或 axiom test。
首先要与 T10 确认系数载体是否捆绑实场的共轭反射对称性、最终范数值域与
命名，以及 T10/T13 对“单个坐标副本内支撑”的标准谓词。数学实现还需要
径向势 curl 恒等式、两类 Urysohn 截断、小尺度阈值选择、坐标球边界处零
延拓和周期化的光滑性、periodic-copies 支撑传递、div-curl，以及 plateau
推出 `eq:bgzero` 的引理。T17 的 `H_ε`、导数/能量/混合范数界不在本草案
范围内。

## 4. 跑了什么命令、什么结果

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Paper1.TorusCube`
  通过（2996 jobs）。
- `cd verification && lake env lean ../research/T16/DraftA.lean` 通过，无错误、
  无警告。
- `make check` 通过（退出码 0）；输出仍显示仓库现有的 copied-source
  `source_hashes_match: false` 诊断及既有 `BoundaryCorollary.lean` 的 `sorry`
  记录，本 lane 未修改这些文件。
- `make test` 通过；仅有依赖树中既有 linter warning。
- `make test-mutations` 通过：`implementation_refactor` 接受，
  `admitted_proof`、`extra_axiom`、`weakened_hypothesis` 均按预期拒绝。
