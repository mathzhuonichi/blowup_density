# 290-SPEC-t12-spec 报告

## 1. 陈述了哪个定理

完成 T12 的 reconciled statement：周期版 Lemma A.1 `lem:calculus` 与均值零
周期版 Lemma B.1 `lem:critical-embeddings`。`MeanZeroSobolevCalculusAPI` 按
reconciliation 的顺序陈述九条 clause：标量 tame product、`H² → L∞`、
`Ḣ¹ᐟ² → L³`、`Λ` 代表存在性、合并的
`‖∇v‖₃ + ‖Λv‖₃`、`‖∇v‖₆ ≤ C‖Δv‖₂`、
`‖v‖H² ≤ C‖Δv‖₂`、谱隙方向以及常数为一的反向
`Ḣ^s ≤ H^s`。这里只交付陈述，没有提供数学证明、添加公理或占位命题。

## 2. Lean 里现在有什么

`research/T12/Spec.lean` 只有一个 Type-valued structure
`BlowupDensity.T12.Draft.MeanZeroSobolevCalculusAPI`。七组常数及其正性先于
九条 theorem fields；字段名、假设捆绑和量词顺序均按 lead reconciliation。
文件按 T13 policy 逐字复制所需的 post-amendment T10 vocabulary；
`IsPeriodicDatum`、`IsPeriodicHomogeneousDatum` 与新标量镜像
`IsPeriodicScalarDatum` 都含 Haar integrability，避免非可积周期场把 total norm
错误降为零。

导数层的 `lift`、`gradientTensor`、`laplacian` 与已注册
`Contracts/V1/GradientL6.lean` 定义同形，并由三个 `example ... := rfl` 固定。
另有两个 `rfl` 检查确认 `CompletedDense` / `CompletedDenseHomogeneous` 分别
definitionally 等于相应的 `CompletedDenseVia` 展开。六个 draft provenance 文件
已从 lane 269/270 原分支逐字复制，并用 SHA-256 比较确认与各自 git blob 一致。

`research/T12/COMPARISON.md` 合并了论文 clause、A/B 来源和逐项 ruling，且
“Proof dependencies”逐字保留 reconciliation 的证明依赖段落。

## 3. 缺口是什么

本 lane 不证明九条 clause。后续 proof lanes 仍需完成 T10 注册桥、周期 Fourier
唯一性和 Parseval、微分/`Λ`/Laplacian 乘子恒等式、谱隙、周期卷积 tame
estimate、`H²` 的加权 `ℓ² → ℓ¹`、一致的均值零临界嵌入，以及向量分量组装；
完整清单见 `COMPARISON.md` 的 “Proof dependencies”。T18 还需要从本 API 导出
pointwise `supNorm_le` 与向量 tame-product interfaces，但 reconciliation 明确不把
它们加入本 structure。

任务 brief 中的 `q : ℝ≥0∞`、`q = 1 ∨ q = 2`、
`criticalOrder q.toReal` 和 R42 insertion references 属于 R46 模板残片；T12 的
binding nine-clause table 没有时间指数或 density clause。因此没有擅加第十条
字段，只按 brief 保留两个 completed-density `rfl` 检查；此点已列入 owner open
question。

## 4. 跑了什么命令、结果如何

- `cd verification && lake env lean ../research/T12/Spec.lean`：通过，0 errors，
  无输出；五个 `rfl` checks 全部 elaboration 成功。
- 六次 branch-blob SHA-256 对比：`DraftA.lean`、`DraftB.lean`、两份原始
  `COMPARISON_*.md`、`REPORT_269.md`、`REPORT_270.md` 全部 `VERBATIM`。
- `git diff --check`，以及对三份 Lean 文件扫描
  `sorry|admit|axiom|native_decide`：通过，无匹配。
- `make check`：通过。输出仍报告基线已知的
  `Paper1/BoundaryCorollary.lean:90` 历史 `sorry` 与
  `source_hashes_match: false`，检查器退出码为 0；本 lane 未导入或修改该文件。
- `make test`：通过，10732 个既有目标完成；仅有既有 linter warnings。
- `make test-mutations`：通过；四类 mutation 均得到预期结果。
