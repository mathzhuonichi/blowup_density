# 269-SPEC-t12-draft-a 报告

## 1. 陈述了哪个定理

完成 T12 的独立 draft A 陈述，覆盖七条目标：周期版 eq:Rproduct、
`H²(T³) → L∞(T³)`、均值零 `Ḣ¹ᐟ²(T³) → L³(T³)`、
`‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖Ḣ³ᐟ²`、`‖∇v‖₆ ≤ C‖Δv‖₂`、
`‖v‖H² ≤ C‖Δv‖₂`，以及均值零场上的谱隙范数比较。这里只交付陈述，
没有加入证明、公理或占位命题。

## 2. Lean 里现在有什么

`DraftA.lean` 把物理场保留为 `R³` 上的单位周期函数，并把分析数据写成
`lp (Fin 3 → ℤ) 2` 的加权 Fourier 系数；非齐次权为
`(1 + 4π²|k|²)^(s/2)`，齐次权为 `|2πk|^s`，零模单独删去，均值零定义为
每个分量的 `k = 0` 系数为零。`∇`、`Λ`、`Δ` 用精确 Fourier 乘子关系
定义弱代表，因此临界陈述不被缩成光滑场版本。七条不等式是
`MeanZeroSobolevCalculusAPI K : Prop` 的独立字段；实常数放在显式参数
`MeanZeroSobolevCalculusConstants` 中，并在 API 中逐一要求正性。这样处理是因为
Lean 的 proof irrelevance 不允许在 `Prop` 结构中直接投影实数数据。

## 3. 还缺什么

本 lane 是双盲规格稿，没有注册合同或证明。所有本地周期 datum/norm/mean-zero
定义仍须与 T10 对齐并建立桥。主要证明缺口是：体积一 torus 上的 Fourier
唯一性与 Parseval、乘子代表存在性、谱隙权比较、周期卷积 tame estimate、
`H²` 系数的 `ℓ¹` 控制，以及不依赖频率支撑的 `H¹ᐟ² → L³` 与
`H¹ → L⁶` 紧流形嵌入。现有有限模 `PeriodicCriticalBridge` 不能充当后一项。
`COMPARISON_A.md` 记录了论文逐条对应、表示选择、歧义、所需引理和 Section 4
的 `TameProduct`、`BoundedRepresentative`、`GradientL6(V2)`、
`HomogeneousNorm` 对应合同。

## 4. 跑了什么命令、结果如何

- `cd verification && lake env lean ../research/T12/DraftA.lean`：通过，无输出。
- `git diff --check` 与对 `DraftA.lean` 的
  `sorry|admit|axiom|native_decide` 扫描：通过，未发现禁用 token。
- `make check`：通过；输出仍列出仓库已知的
  `Paper1/BoundaryCorollary.lean:90` 历史 `sorry`，本 lane 未导入或修改它。
- `make test`：通过；10732 个既有测试目标完成，仅有既有 linter warning。
- `make test-mutations`：通过；mutation 检查退出码为 0，仅有既有 linter warning。
