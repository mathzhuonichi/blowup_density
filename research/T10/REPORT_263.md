# Lane 263-SPEC-t10-draft-a report

## 1. 证了哪个定理

本 lane 不证明分析定理；它独立起草了 T10 周期数据层的合同陈述。草稿固定了
Section 3 后续结论所用的对象：`H^s(T^3)` 加权系数数据、物理场桥、均值与均值零
分解、周期 Leray 投影、压力零均值规范、`X_T`、`F_T`、经典解、最大寿命、爆破集、
相对密度及 `E_T`。

## 2. Lean 里现在有什么

`research/T10/DraftA.lean` 是只 import `Mathlib` 的 definitions-only 草稿，并已通过
Lean 4.34.0-rc2 elaboration。核心载体是按频率索引、值为三维复 Euclidean 向量的
`lp ... 2`；数据本身储存 `(1+4*pi^2|k|^2)^(s/2)` 加权后的 Fourier 系数，实物理场
通过共轭反射约束。Leray 使用每个频率上到 `span{k}^perp` 的正交投影，因而零模为
恒等。`ClassicalSolutionT` 是新合同结构，所有周期性、方程和压力规范均按 `[0,T)`
或 `(0,T)` 的论文区间显式陈述。

`research/T10/COMPARISON_A.md` 给出逐项 paper-to-Lean 对照、`2*pi` 归一化、复系数
编码实场、物理周期性的量词、是否复用本地结构等全部选择，并记录歧义和 T11+ 所需
引理。

## 3. 缺口是什么

本草稿尚未进入 `verification/Contracts/V1/TorusData.lean`，也没有 binding/tests。
主要证明缺口是 `TorusCube` 定义桥和向量 Parseval、datum 唯一性/存在性、零模等于
空间均值、Leray 的坐标公式与收缩/投影/交换性质、物理散度与系数散度等价、压力
归一化保持方程、系数 `E_T` 与物理能量范数等价、均值演化及均值零保持，以及新
`ClassicalSolutionT` 与现有周期局部解结构的逐字段双向转换。完整清单在 comparison
文件的 “Needs a lemma” 一节。

## 4. 跑了什么命令、什么结果

- `. scripts/lean-env.sh && (cd verification && lake env lean ../research/T10/DraftA.lean)`：
  成功，0 errors，0 warnings。
- `git diff --check`：成功，无 whitespace error。
- 对 `DraftA.lean` 扫描 `sorry|admit|axiom|native_decide`：无匹配。
- 检查直接 import：只有 `import Mathlib`。
