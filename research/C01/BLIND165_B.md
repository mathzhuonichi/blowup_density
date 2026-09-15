# C01 独立盲稿 B

## 证了哪个定理

本次只拟定完整陈述，不提供存在性见证或证明。范围为全空间论文 §4 的 ordinary energy、H¹ 吸收及 H² 时间积分：`paper/sections/04-whole-space.tex:106–131`，并覆盖 `:171` 的复用。直接继承冻结 V3，因而 V1/V2/V3 的全部字段及常数保持原样。

## Lean 里现在有什么

`BLIND165_B.lean` 新增 enstrophyIdentity、enstrophyAbsorption、enstrophyIntegrated、laplacianTimeIntegral、sobolevTwoFourier、h2TimeIntegral，以及三个独立于所有输入的正实常数。

来源和独立选择：

- §4:106–112：对负 Laplacian 测试。导数为 `-2ν D + 2 advectionWork - 2 pairing f Δu`；特别审计了两个符号。冻结 C₁ 已经是 L³ 版本的常数，故阈值采用 `‖u‖₃ ≤ ν/(4 C₁)`，不是把原文 y 与 L³ 混为一物。
- §4:113–116：吸收后梯度平方导数加 **ν** 倍 Laplacian 平方，右侧 **C ν⁻¹** 倍 force 平方。可选 C=2 的 Young 分配，但稿件不钉死非必要数值。
- §4:117–120：ordinary L² estimate 无小量条件，由 V3 原样提供；不能用 Laplacian 把低频丢掉。K(S) 含非零初始 L² norm。
- §4:121–130：S 为有限实数，允许 S=T，且这里推广到 S=0 的平凡情况。Laplacian 积分界包含 `ν⁻¹ gradientSq a` 和 `C ν⁻² ∫ force²`。H² 界另外包含 `C S K(S)²`。三个项都保留。
- §2:12–15、29–30：输入 H∞，所有紧子区间的 Sobolev 连续性；不额外假设 temporalDerivative 属于 L²、gradientSq 可微或导数可积。
- `appendix-a-local-theory.tex:65–76`：论文说明由方程恢复时间 Sobolev 正则性。这应是证明工作，不是额外 API 输入。
- `appendix-b-embeddings.tex:12–24,26–37`：固定维数/指数的普适常数及 smooth H∞ 适用性。
- `Contracts/V1/Data.lean:131–162,624–648`：采用冻结角频率 `IsSobolevDatum` 和真实 `RealVectorSobolev 2` norm；未使用 cycles Fourier norm，未把 H² 偷换成 `l2Sq + laplacianSq` 的定义。

常数量词：C₁ 继承，CRH1/CH2/Cassembly 均为结构字段，因此在 ν、a、f、T、w、S、datum 之前。它们不是每个解存在一个数。没有要求三个不同用途的 C 数值相等。

时间边界：导数在 Ioo 0 T；点值在 Ico 0 T；积分用 Ioo 0 S，端点零测度，与通常从 0 到 S 的积分一致。S=T 时从不读取 w.velocity T。吸收只在需要估计的 Ico 0 S 上假设，未要求整个较长 lifespan 都小。对 t 的积分估计仅需 t 以前的小量，梯度点值由连续性得到。

积分非空洞性：Laplacian 与 H² 平方均显式得出 IntegrableOn，再附数值界。H² 对任意在 Ioo 0 S 表示速度的 datum path 陈述；不额外要求路径连续或可测，这些在经典解类由 datum 唯一性和已有 Sobolev path 推出。

## 缺口与疑义

1. 尚未编译或证明；尤其 namespace、父结构字段解析交由后续 Lean 检查。未声称可运行。
2. Fourier 项只对 MemHInfty 陈述，足以覆盖所有论文使用的速度；没有扩张为最弱 H² 分布版本。
3. H² 积分界是原论文直接列出的核心输出；零初值版可代入 a=0 消去梯度初能，无需重复字段。此稿未加入 critical H½ 能量、Gronwall、bootstrap 或 continuation 结论，均非本 a priori 合同范围。
4. enstrophyIdentity 与 endpoint Laplacian estimate 是原文测试及“controls ... integral”明确隐含的展开，不是原文单独编号定理。
5. 指定路径仅在开时间区间的表示条件不会损失端点初能，因为初能来自 w.initial 和已有经典正则性，不来自 G(0)。

## 跑了什么

仅 PowerShell 定向读取论文、冻结合同和 CLAUDE.md，写入本稿两文件；未读实现、其他研究稿、C01/Spec.lean 或另一代理内容，未执行 Lean/lake/Git。未做编译或视觉验证。
