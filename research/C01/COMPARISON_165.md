# C01 lane 165 陈述协调记录

## 结论与范围

A、B 两个独立盲稿冻结后，本轮获准对读 B 与原 `research/C01/Spec.lean`。拟定 `verification/Contracts/V4/EnergyAbsorption.lean`，由 `EnergyAbsorptionAPI extends EnergyAbsorptionPartialV3API` 完整保留 V3 及祖先所有字段。新增原 Spec 的六个字段和三个正的全局常数，字段类型逐字提取原 Spec，未从实现能力反推或削弱规范。

没有增加 Absorbs、AbsorptionOn、h2Integral 等别名，没有引入 datum 路径参数，没有增加终端 Laplacian 公有字段，也没有重新捆绑 GradientL6API。后者已有单独冻结接口，C01 既有 C₁ 与 trilinear 字段保持继承形态。此版本仍仅是结构声明，没有存在断言或实例。

## 逐字段来源与选择

以下论文行号均为 `paper/sections/04-whole-space.tex`。

| 新字段 | 原 Spec 行 | 论文行 | 协调结果 |
|---|---:|---:|---|
| CRH1 / CH2 / Cassembly 及正性 | 266–279 | 115 / 123 / 127–130 | 三个常数在所有 ν、数据、解、时间之前全局选择；不钉具体数值 |
| enstrophyIdentity | 487–495 | 106–112 | 精确测试 -Δu，真实 HasDerivAt；导数值为 2N−2νD−2F |
| enstrophyDifferentialBound | 510–520 | 112–115 | 保留 ENNReal.ofReal C₁ 乘 criticalL3 的阈值 ν/4；右边 CRH1 ν⁻¹||f||² |
| enstrophyIntegralBound | 532–543 | 114–117 | 0≤t<T；[0,t) 吸收；IntervalIntegrable 与实区间积分界同时为结论 |
| sobolevTwoFourier | 555–558 | 121–124 | Data.sobolevENorm 2 的 ENNReal 实指数 rpow 2；前件仅 MemHInfty |
| h2TimeIntegral | 576–588 | 119–130 | 0<S≤T；(0,S) 上实际 H² 下积分；含三项 CSK²、Cν⁻¹梯度初值、C(ν⁻¹)²力平方积分 |
| h2TimeIntegralZeroDatum | 599–607 | 137–141、171 | 相同 Cassembly；去掉初始 L² 与初始梯度项，其余时间与阈值完全一致 |

普通能量恒等式、微分界、eq:RL2，以及 velocityJets、forceTimeRegularity、三线性界、Laplacian 范数转换由 V3 原样继承。来源是第117–120行，以及 `02-preliminaries.tex:136–149` 的普通能量与正则化范数除法。它们仍负责低频，不能由吸收估计替代。

## A、B 与原 Spec 的实质比对

### 1. 中间积分的收敛性

A 的 `enstrophyIntegralBound` 只有实区间积分界，遗漏显式 `IntervalIntegrable` 结论。尽管从经典解局部 H∞ 连续性可推出它，但单独使用 totalized 实积分界会丢失这项可消费保证。最终恢复原 Spec 的 `IntervalIntegrable … volume 0 t ∧ …`，不是增加假设。

B 已有 `IntegrableOn … (Ioo 0 t)`，在 0≤t 下与原 Spec 的 IntervalIntegrable 等价：实 Lebesgue 测度无原子，开闭端点差有限零测集，且区间方向为正。最终采用已有 interval integral 词汇，使该保证与普通能量原语一致。

### 2. B 的 datum 路径与真正 Sobolev 范数

B 的 Fourier 字段对每个代表同一物理场的 A 断言 ||A||² 界，H² 字段对每个逐点代表路径 G 断言其平方范数可积及界。它没有要求 G 额外连续或可微。

在当前类上 `ClassicalSolutionR.sobolev` 已提供连续的 order-2 datum 路径；`IsSobolevDatum` 的唯一性使 B 中任一 G 在 (0,S) 与该路径逐点相同。因此连续性/可测性来自解自身，而不是新正则性前件。`sobolevENorm` 与唯一 datum 的范数桥把 B 的 ||G(t)||² 变成原 Spec 的实际角 Sobolev 范数平方。非负可测函数的有限下积分与实积分可积及相同积分值相联系，故两种表述在当前类上可协调。

最终直接使用原 Spec 范数，不增加 G 参数或存在 datum 的新前件；也不以 L²+Δ 图范数替换 H²。桥的证明仍是实现义务，不能仅因为使用下积分就省略可测性。

### 3. 时间窗口与终端

两盲稿 H² 允许 S=0，这是空区间与零右边的平凡扩张，不是论文延拓论证所需。最终保留原 Spec `0 < S → S ≤ T`。

有末端梯度值的积分字段保持 t∈[0,T)，不能改成 t≤T；ClassicalSolutionR 的总函数在 T 处并无约束。H² 字段仍必须允许 S=T，积分是 (0,S)，因而不要求 u(T)。论文第121行明确说 within or at the maximal lifespan，第127–130行据此排除有限终点。

A、B 的独立 terminal Laplacian 字段均是有价值的中间后果：先对 t<S 用 enstrophyIntegralBound，丢掉非负末端梯度、除 ν，再单调收敛至 S。它不是原 C01 六字段之外的新公有义务，故不另加字段。没有丢失原接口内容：局部积分界仍带末端梯度和收敛结论，H² 仍完整覆盖 S=T。实现可以保留此终端引理来证明 H² 字段。

### 4. 阈值、符号和幂

A 的阈值与原 Spec 相同。B 的 ||u||₃≤ofReal(ν/(4C₁)) 在 ν>0、C₁>0 下与 ofReal(C₁)||u||₃≤ofReal(ν/4) 等价；C₁ 有限严格正，故可在 ENNReal 中合法消去，不会产生 0·∞ 漏洞。最终选择乘法形态，直接接父 trilinearAbsorbed。论文第110行的 C₁ 已吸收半阶到 L³ 的嵌入常数，与父接口乘 L³ 的 C₁ 不宜混同；第93、171行负责下游嵌入。

A、B 写 -2νD+2N−2F，原 Spec 写 2N−2νD−2F，实数交换结合律给出相同符号；最终沿原 Spec 次序，尤其 forcing work 的负号不可改变。

微分 RHS 为 CRH1 ν⁻¹F²，积分后丢梯度并再除 ν 得 CRH1 (ν⁻¹)²∫F²。A 的 ν⁻² 数学意图相同，B 的逆元平方亦相同；最终写原 Spec `(ν⁻¹) ^ 2`，消除负指数记号的解析歧义。

A 的 ENNReal natural square 与原 Spec 的 real-exponent rpow square 用 `ENNReal.rpow_natCast` 等幂转换协调；B 的 datum 实数 norm square 先通过范数桥与 ENNReal.ofReal 的乘法/幂转换。最终两处 Sobolev 平方统一为 `(2 : ℝ)`；实数 K 的平方与逆元平方保持自然数 2。这里是显式代数协调，不是范数或粘性尺度变化。

### 5. 常数不应过度规定

从 Fourier 权重可推 CH2=2，Young 可推 CRH1=2，相应可选 Cassembly=4；A 记录的是可选锐利程度，不是论文规范。论文只要求全局正有限常数。实现选合法较宽的 2/16/32，只要全部字段共享且可证明，完全符合最终合同。未加入常数之间的额外等式或归一化；不因实现困难调整数据类、正则性、时间端点或 ν 次幂。

## 验证与剩余步骤

本轮只写 V4 合同与本比较记录。没有运行 Lean/lake，没有写 Bindings、注册清单、Tests 或全局记录，也没有 commit/push。六个新数学字段的源文本与原 Spec 做逐字段比较；这只验证类型源文本一致，不能替代 Lean elaboration 或独立数学复核。待 root 与 B 独立复核后，由 Luna 编译。
