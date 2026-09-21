# Lane 281 / T22 reconciled specification report

## 1. 证了哪个定理

本 lane 是 statements-only reconciliation，没有证明新定理、没有构造
`BoundedDomainNormAPI` 的实例，也没有加入公理或证明占位。交付的
`Spec.lean` 按 `research/T22/RECONCILIATION.md` 的绑定裁决，精确陈述
`paper/sections/03-torus.tex:600-630` 的三个目标事实：限制分布定义的
`H^s(Omega)` 商范数在零阶等于通常的向量 `L²(Omega)` 范数；固定光滑紧支截断在
任意实阶 `H^s(R³)` 上是有界乘子；固定 `K compactly contained in Omega` 时，光滑
且支撑于 `K` 的场满足零延拓双边比较。比较常数在场 `z` 之前选择，所以统一适用于
同一 `K` 内的较小支撑和收缩 `epsilon` 族。

## 2. Lean 里现在有什么

`research/T22/Spec.lean` 保留 Draft B 的定义和三字段 API：`DomainTest`、
`DomainFunctional`、`restrictDatum`、`domainSobolevENorm`、`restrictField`、
`zeroExtension`、`IsCutoffDatum`，以及 `BoundedDomainNormAPI.orderZero`、
`cutoffMultiplier`、`zeroExtensionComparison`。每个 API 字段的 docstring 都记录了
论文行号、精确量词顺序和 non-vacuity；商范数显示式本身是定义，没有增加同义反复的
字段；也没有声称任意 `H^s(Omega)` 元素都有有界零延拓。

词汇选择遵守 reconciliation §3：本文件 import `Contracts.V1.Data`，直接复用已注册的
`SpatialField`、`RealVectorSobolev`、`angularRealization`、`FourierData` 和
`sobolevENorm`。没有 import 不能作为模块使用的 `research/T10/Spec.lean`，也没有复制
任何 T10 定义，因为 T22 的两个显示式只涉及 `R³` 和 `Omega`，不出现环面对象。这个
选择和原因已写进 `Spec.lean` 头注释及 `COMPARISON.md`。

`COMPARISON.md` 给出逐条 paper clause → Lean declaration 表，合并 A/B provenance 和
lead ruling；另有量词/non-vacuity 审计、细化后的 proof dependencies、对 T10
“Needs a lemma” 条目的逐项交叉说明，以及 owner open questions。结论是：T22 证明所需的
T10 周期引理集合为空；真正缺的是连续频率 `R³` 的零阶向量 Plancherel/限制商计算和任意
实阶空间截断乘子分析。

按 provenance 要求，`DraftA.lean`、`COMPARISON_A.md`、`REPORT_275.md` 从 lane 275，
`DraftB.lean`、`COMPARISON_B.md`、`REPORT_276.md` 从 lane 276 逐字复制；逐文件 Git blob
hash 与源分支完全一致。

## 3. 缺口是什么

这是规范，不是证明。后续 proof lane 仍需：补齐 order-zero angular datum 与向量
`L²(R³)` 范数的等距 Plancherel（现有 `OrderZeroDatum.lean` 明确只证明 datum 存在，未证明
范数恒等式）；证明 `L²` 限制收缩与零延拓等距；构造 `K` 邻域内、支撑于 `Omega` 的
光滑截断；建立任意实数 `s` 的 Bessel weight ratio、Fourier 乘积/卷积、Schwartz 衰减、
Young `L¹*L²→L²` 和实对称性保持；最后完成 distributional cutoff identity 及
`ENNReal.iInf` 记账。

`HomogeneousPartial.annularRestriction` / `annularSmoothing` / `annularSchwartz` 是频率环带
逼近，不能直接充当空间截断乘子；`TameProductAPI.tameProductVector` 只覆盖带更强假设的
整数阶，若走插值路线还缺任意实阶插值定理。论文 lines 627-629 的 mixed-time 推论需要
强可测 datum path 和 Bochner norm 比较，按三字段裁决留给 T23。owner 还需决定将来是否
注册真正的区域分布对偶 carrier、是否保留任意开域的更强一般性、是否把 mixed-time
桥放进 T22 V2，以及是否扩展到一般有限维 tensor carrier。

## 4. 跑了什么命令、什么结果

- `cd verification && lake env lean ../research/T22/DraftA.lean`：exit 0，零错误。
- `cd verification && lake env lean ../research/T22/DraftB.lean`：exit 0，零错误。
- `cd verification && lake env lean ../research/T22/Spec.lean`：exit 0，零错误、零输出。
- 对六个 provenance 文件分别比较源分支 `git show ... | git hash-object --stdin` 与本地
  `git hash-object`：全部 hash 一致。
- `. scripts/lean-env.sh && make check`：exit 0；13 个 contract-policy tests 和 45 个
  work-item 检查通过。输出仍报告仓库既有的
  `formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90` `sorry` 和
  `source_hashes_match: false` 状态；本 lane 没有修改或 import 该文件。
- `. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make test`：exit 0；全部已注册合同测试通过，
  输出中的 linter warnings 均来自既有依赖。
- `. scripts/lean-env.sh && make test-mutations`：exit 0；implementation refactor 被接受，
  admitted proof、extra axiom、weakened hypothesis 均按预期被拒绝。
- `git diff --check` 及对 `Spec.lean` 的 `sorry|admit|axiom` 扫描：通过，无命中。
