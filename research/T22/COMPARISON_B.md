# T22 独立陈述草稿 B

仅依据指定论文、注册 D01/B02 模板及任务卡；未读取任何其他 T22 草稿或 T10/T12/T13/T16 研究目录、其他 lane 简报。没有证明或 API 实例。

## 论文条款与 Lean 对应

| 论文 | Lean 定义 / 字段 | 量词与范围 |
|---|---|---|
| `03-torus.tex:601-606`, eq:restriction-norm | `DomainTest`, `restrictDatum`, `domainSobolevENorm` | 任意实阶；对全部 `RealVectorSobolev s` 分布延拓取 ENNReal 下确界；无延拓时为 ∞ |
| `03-torus.tex:606-607` | `BoundedDomainNormAPI.orderZero` | ∀ 开 Ω，∀ Ω 内光滑 z；区域范数等于 `eLpNorm z 2 (volume.restrict Ω)` |
| `03-torus.tex:617-624` | `IsCutoffDatum`, `cutoffMultiplier` | ∀ s，∀ 固定光滑紧支实 χ，∃ C > 0，∀ A，∃ B，B 表示 χA 且范数 ≤ C‖A‖ |
| `03-torus.tex:608-626`, eq:zero-extension | `zeroExtension`, `zeroExtensionComparison` | ∀ Ω K，开性、紧性、K ⊆ Ω，∀ s，∃ C > 0，∀ z，Ω 内光滑且零延拓支撑 ⊆ K ⇒ 双边界 |
| `03-torus.tex:626-629` | 上一字段中 C 在 z 之前选取 | 同一个 C 可用于所有 ε、所有时刻，只要支撑都在同一 K；混合时间范数是待推导推论，未额外添加 API 字段 |
| `03-torus.tex:630-631` | D01 `RealVectorSobolev` / `Space` | 欧氏三向量分量平方和范数；本草稿不另做一般张量推广 |

商范数显示式本身是定义，不再添加展开定义的恒等式字段。API 的三个命题字段均有实际数学内容；不是待指定的 Prop 参数。

## 表示选择

- ℝ³ 侧直接 import `Contracts.V1.Data`，逐字使用 `RealVectorSobolev`、`angularRealization`、`FourierData`、`SpatialField`、`sobolevENorm`；不重定义、不改注册合同。`IsSobolevDatum` 是其既有物理场桥。
- 区域分布用对紧支 Schwartz 测试的作用表示。`DomainFunctional` 是函数空间这个环境载体；有限 Sobolev 对象取 `restrictDatum` 的像。商范数对数据见证取下确界，不把负阶分布误限制为普通函数。
- `restrictField` 用 Ω 上积分，域外值完全不参与。`zeroExtension` 是 Ω 的 indicator；支撑条件写在它上面，所以输入的域外值不被错误约束。仅要求 `ContDiffOn`，没有额外要求输入在边界或域外光滑。
- 乘子用测试函数的转置作用定义，未把物理场乘法当作对一般分布的定义。固定光滑紧支 χ 保证 Mathlib `smulLeftCLM` 的 temperate-growth 条件成立；该工具在没有此条件时的总化行为不用于任何字段。
- `ENNReal.ofReal C` 中 C 是严格正的有限实数；没有 `.toReal` 将 ∞ 变成 0 的问题。`sobolevENorm` 的 D01 配对总化风险在光滑紧支零延拓上不可达。
- 全部新局部定义已标注 “needs registration / to be aligned with T10”。不是声称它们已在 T10 注册，也不是复制不可见草稿。注册时应逐字移入允许的合同数据模块并加定义桥。

## 歧义与边界

1. 任务描述提到 cube；论文显示式写一般 Ω，后文推论允许 bounded box 或 bounded smooth domain。这里保留任意开 Ω：证明只用 K 紧且包含于 Ω，不用有界性或光滑边界；当然覆盖开立方体。
2. §1 的周期物理场 / 加权 `lp (Fin 3 → ℤ) 2` 约定仍然有效，但这两个显示式完全在 ℝ³ 与 Ω 之间，不出现周期范数。硬加周期系数层会扩大 T22。T23 若要从周期场限制到 Ω，需另外结合固定截断和 T10 的桥。
3. “usual L²” 的额外字段目前在 Ω 内光滑物理场上陈述，覆盖本节点使用场景；没有宣称提供所有 L² 等价类的完整 Banach 商空间构造。一般分布的商范数定义则不限于光滑场或正阶。
4. 固定 K 的约束不能换成随 ε 逼近边界的 Kε；也没有给任意 H^s(Ω) 元素一个有界零延拓算子。
5. `03-torus.tex:627-629` 的时间推论需要可测性及 Bochner 商空间桥，不应仅以一个未经可测性检查的下积分替代。当前交付限两个空间显示式及其乘子论证。

## Needs a lemma

- 紧支光滑测试与 Schwartz 测试子类型的对应；限制数据等价关系及商空间 Hilbert 范数实现。
- `domainSobolevENorm` 与标准分布限制商范数一致；阶零与区域 L² 一致（包括无有限延拓的情形）。
- 任意实 s 的光滑紧支乘子界：论文加权比估计、Fourier 卷积公式、Schwartz 衰减和 Young L¹ * L² → L²，含 angular normalization 常数。
- 光滑紧支实 χ 的复值化有 temperate growth，测试乘法与 `smulLeftCLM` 一致。
- K 紧含于开 Ω 时构造 χ ∈ C_c^∞(Ω)，在 K 邻域恒为 1。
- Ω 内光滑且零延拓支撑在 K 的场，其零延拓全局光滑紧支；任意实阶都有 D01 datum，范数有限且 datum 唯一。
- 对每个分布延拓 A 证明 χA = E₀z；由统一乘子界经过下确界得到上界，下界由 E₀z 本身作为延拓见证得到。
- 固定 K 的 ε / 时间族直接实例化同一个 C；混合时间范数需要强可测路径及标准 Bochner 范数比较。张量推广需有限 Euclidean 分量积版本。

## 第 4 节对应物与复用

D01 `Contracts/V1/Data.lean:150-260` 是数据 / 实现配对 / ENNReal 范数记账架构，本草稿原样复用其全空间对象。`:375-410` 的齐次 / Fourier 范数不是本节点的非齐次负阶替代；`:509-580` 的力类和时间路径可用于后续时间推论，但不作为空间字段的额外假设。

B02 `Contracts/V1/HomogeneousPartial.lean` 的 `annularRestriction`、`annularSmoothing` 在所有实阶给数据侧环带截断与光滑逼近；V2 通过继承保留原字段。它们的 ℝ³ 载体和适用结论可以原样使用，但它们是频率环带操作，不是空间 χ 的任意实阶乘子定理，不能直接充当 `cutoffMultiplier`。B02 齐次低频阶数限制也不应移植到本节点。

任务卡两个 `Boundary*` 文件给 PDE / 支撑 / no-slip 记账，不提供目标商范数与乘子分析。仅阅读其证据，不 import 它们的依赖链。T22 不包含 no-slip 解存在性、唯一性或 T23 插入结论。
