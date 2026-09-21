# 275 / T22 draft A report

## 1. 证了哪个定理

本 lane 按“statements only”交付了 T22 的双盲 A 稿，没有加入证明或公理。`BoundedDomainNormAPI` 逐项陈述
`paper/sections/03-torus.tex:600-630` 的有界区域范数层：任意实数阶（含负阶）的限制商范数、零阶与通常
`L^2(Omega)` 范数的一致性、固定内部紧集上的光滑零延拓双边估计，以及固定空间截断在
`H^s(R^3)` 上的乘子界。常数的类型是 `C Omega K s`，量词位于场和缩放参数之前，因此不依赖较小支撑或
收缩尺度 `epsilon`。

## 2. Lean 里现在有什么

[`DraftA.lean`](DraftA.lean) 只 import `Contracts.V1.Data`，逐字复用 D01 已注册的 `SpatialField`、
`RealVectorSobolev`、`IsSobolevDatum` 和 `sobolevENorm`。本地新对象都显式标为“needs registration / to be
aligned with T10”：零延拓、带 datum 的有效全空间延拓、区域商范数、区域 `L^2` 范数、紧包含/有界开域谓词、
空间截断乘法和固定支撑光滑类。限制关系与截断恒等式使用 a.e. 相等；商中的延拓另带 Schwartz 配对可积性，
避免 D01 文档记录的 totalized-integral 假零 datum 漏洞。

[`COMPARISON_A.md`](COMPARISON_A.md) 给出 paper clause 到 Lean 字段的逐行表、量词选择、歧义、待证引理，
并说明 Section 4 的复用边界：D01 的 R3 datum 层可逐字复用；B02 的 `annularRestriction` / `annularSmoothing`
只复用陈述架构，不能把频率环带结论当作这里的空间截断乘子；`BoundaryAnalyticBridge` 和
`BoundaryReferenceRestriction` 留给 T23 的无滑移/见证记账。

## 3. 缺口是什么

这是一份规范草稿，所有 API 字段仍待证明。核心分析缺口是：内部光滑截断的构造、任意实数阶的角频率
`H^s` 截断乘子定理（含实值对称性和 Schwartz 配对可积性）、零阶商范数计算、以及对 `iInf` 取下确界的装配。
论文 `03-torus.tex:627-629` 的 Bochner 时间范数提升没有伪装成 pointwise-infimum 积分字段；它需要先注册真正的
`H^s(Omega)` 商空间/可测延拓路径，或在 T23 中补一个无 lower-integral gap 的提升引理。旧的
`BoundaryCorollary.domainSobolevNorm/domainForceNorm` 是标量、旧 Sobolev carrier，且没有零延拓比较，不能直接充当
T22 绑定。

## 4. 跑了什么命令、什么结果

- `cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T22/DraftA.lean`：通过，零错误。
- 用临时 `#check` 文件核对了 `IsCompact`、`IsOpen`、`Bornology.IsBounded`、`HasCompactSupport`、`tsupport`、
  `ContDiff`、`Integrable`、`AEStronglyMeasurable`、`eLpNorm`、`ENNReal.ofReal`、`SchwartzMap`、
  `RealVectorSobolev`、`IsSobolevDatum`、`sobolevENorm`；全部解析成功，临时文件已删除。
- `. scripts/lean-env.sh && make check`：退出码 0；架构、合同政策与工作队列检查通过。输出仍报告仓库既有的
  `formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90` `sorry` 和 source-hash 状态；本稿没有 import
  该模块，也没有新增 `sorry` / `admit` / `axiom`。
- `. scripts/lean-env.sh && make test && make test-mutations`：退出码 0；全部注册合同测试通过，mutation suite
  的 implementation refactor 被接受，admitted proof / extra axiom / weakened hypothesis 均按预期被拒绝。输出中的
  linter warning 均来自既有依赖。
