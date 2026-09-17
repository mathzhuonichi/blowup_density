# 272-SPEC-t16-draft-b

## 1. 证了哪个定理

本 lane 只写陈述，没有证明定理。目标是 `03-torus.tex:176–215` 的 lem:potential：径向向量势、光滑截断、周期无散修正及 eq:bgzero 的开邻域结论。遵守双盲限制，未读取其他 T16/T10/T13 研究目录内容或相关 briefs。

## 2. Lean 里现在有什么

`DraftB.lean` 包含 `LocalPotentialAPI … : Prop`、承载见证的 `CutoffData`、精确量词的 `localPotentialStatement`，以及需要与 T10 对齐的周期物理层定义。Euclidean curl/cross/缩放直接复用已注册合同。空间支撑写成整数平移球并集，避免错误要求非零周期场在 R³ 紧支撑。`COMPARISON_B.md` 给出条款映射、量词/表示选择、Section 4 I02 对应物及待证引理。更新了 NEXT_SESSION.md。

## 3. 缺口是什么

API 尚无 inhabitant，未注册 Contracts/Bindings/Tests。后续需双盲 reconciliation、T10 词汇对齐、局部径向势证明以及周期零延拓/支撑桥。T16 没有 Sobolev 估计，所以本文件未添加未使用的 Sobolev/齐次范数定义；这些属于 T10/T17。坐标球采用半径小于 1/2 的注入图。首次 elaboration 发现 `Space` 是 EuclideanSpace 而非裸函数类型，整数格点嵌入改用 `WithLp.toLp 2` 后通过。

## 4. 跑了什么命令、什么结果

- `. scripts/lean-env.sh; cd verification; lake env lean ../research/T16/DraftB.lean`：通过，无报错。
- `lake env lean /tmp/t16check.lean`：核对 ContDiffOn、tsupport、HasCompactSupport、EuclideanSpace、spatialDivergence、curl、scaledSpatialCutoff、scaledPacket、tsum、IsCompact、Metric.ball 等实际类型。
- `make check`：通过；37 注册合同、13 policy tests、45 work items。检查输出仍列出基线 BoundaryCorollary 的既有 admission 和 source hash 状态，本 lane 未修改这些模块。
- `make test`：完成到 10732/10732，注册合同类型和标准公理审计通过。这些测试不证明新草案。
- `make test-mutations`：通过，implementation_refactor accepted；admitted_proof、extra_axiom、weakened_hypothesis 均按要求 rejected。

仅本地提交；不 push、merge 或 rebase。
