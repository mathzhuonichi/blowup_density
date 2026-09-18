# 295-SPEC-t17-draft-b

## 1. 证了哪个定理

完成了 `lem:correction`（`03-torus.tex:218-285`）的双盲 B 版 Lean 陈述；
本 lane 只写合同陈述，不提供证明。

## 2. Lean 里现在有什么

`DraftB.lean` 明确定义了 `H_ε`、重标度轮廓及周期混合范数，并用
Type-valued `CorrectionAPI` 收齐导数界、`eq:wE`、`eq:Hmixed`、经 T13 的
`eq:HHs`。所有范数常数有限，能量/混合范数附带 `MemLp` 条件。

## 3. 缺口是什么

主要待证项是 T16 到固定轮廓的缩放恒等式、周期混合范数缩放，以及把
`PeriodicCorrectionEndpointRates` 的整空间端点界经 T13 转移到环面。
细目见 `COMPARISON_B.md`。

## 4. 跑了什么

`cd verification && lake env lean ../research/T17/DraftB.lean`：通过。
