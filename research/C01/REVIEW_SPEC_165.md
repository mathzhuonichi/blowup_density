# C01 V4 陈述独立复核（B，165）

## 结论：ACCEPT

接受 `verification/Contracts/V4/EnergyAbsorption.lean` 当前未注册结构的数学陈述。它保留冻结 V3 全部字段，六个新增数学字段与原 `research/C01/Spec.lean:487–607` 一致，忠实表达论文 `04-whole-space.tex:106–130,171` 的 C01 范围。没有发现需要修改合同的新增假设、范数替换、常数量词变化或时间端点漏洞。

此结论是源代码和数学语义复核，**不是编译通过或传递公理审计结论**。本次未运行 Lean/lake/Git；也未编辑合同、实现或台账。

## 逐项核对

| V4 位置/字段 | 论文与原 Spec | 判定 |
|---|---|---|
| :32 extends V3 | 原 ordinary energy、velocityJets、forceTimeRegularity、trilinear、Laplacian conversion | 原样继承，未削弱 ordinary L² 对低频的独立控制 |
| :34–41 CRH1/CH2/Cassembly | Spec :266–279；论文 :115,123,127–130 | 三个正实结构字段在所有 ν、a、f、T、w、S 之前，普适有限；没有按解选择常数 |
| :44 enstrophyIdentity | Spec :487–495；论文 :106–112 | 导数存在性保留；2N−2νD−2F 符号及因子正确，压力消失是证明义务 |
| :54 enstrophyDifferentialBound | Spec :510–520；论文 :112–115 | 吸收条件 C₁‖u‖₃≤ν/4；导数加 νD，右侧 CRH1 ν⁻¹F²；输入任意导数值不削弱，因为上一字段提供实际导数 |
| :65 enstrophyIntegralBound | Spec :532–543；论文 :114–117 | t∈Ico 0 T；[0,t) 小量；IntervalIntegrable 是结论；保留 gradientSq a，未把初值默认为零 |
| :77 sobolevTwoFourier | Spec :555–558；论文 :121–124 | 实际 angular sobolevENorm 2 平方，仅 MemHInfty 前件；不是定义成图范数 |
| :83 h2TimeIntegral | Spec :576–588；论文 :119–130 | 0<S≤T，Ioo 积分不取 u(T)，三项 CSK²、Cν⁻¹初始梯度、Cν⁻²力平方全保留 |
| :96 h2TimeIntegralZeroDatum | Spec :599–607；论文 :137–141,171 | 相同 Cassembly；初始 L² 与梯度项消失，其余不变 |

阈值中的父 C₁ 是 L³→三线性吸收版本，不应逐字等同原文把半阶嵌入也吸收进去的 C₁y。V4 沿冻结父字段选 L³ 小量，论文 :109、:171 明确支持；半阶嵌入和 bootstrap 留给下游，并未假设它们已成立。B 盲稿除法阈值与此乘法阈值在 ν>0、C₁>0 下等价，不存在 0·∞ 消去问题。

B 的 S=0 扩展和单独 terminal Laplacian 字段并非原 Spec 必须增加的公有字段。删除这两个冗余扩展没有削弱原 C01 六字段。一般终端耗散估计可由 t<S 的 enstrophyIntegralBound、非负梯度、除 ν 和单调收敛导出；H² 字段本身仍覆盖 S=T。

## 核心语义审计：下积分与 datum 实积分

**有限的下积分本身不能对任意函数推出可测性。** 不能以“ENNReal.ofReal RHS 有限”一个理由声称已经表达了论文的 Bochner/Lebesgue 可积性。但这里的实际经典解已有足够条件，以下链条验证了这一点：

1. 冻结 `Data.lean:643–645` 的 `ClassicalSolutionR.sobolev 2` 提供 H : ℝ→RealVectorSobolev 2，H 在 Ico 0 T 连续，并在每个该区间的 t 表示 u(t)。对 0<S≤T，Ioo 0 S 包含在 Ico 0 T 内；即便 S=T，H 在这个开区间仍连续，无需在 T 延拓。
2. `D01/ForceClass.lean:286–294` 的 `isSobolevDatum_unique` 已有实际证明：分别比较三个分量的 angularRealization，经其单射得到 A=B。没有额外正则性或可测性参数。冻结 `Contracts/V1/DatumLemmas.lean:284` 也已公开该唯一性义务。
3. `A04/Forcing.lean:126–130` 的 `sobolevENorm_eq` 已证明：IsSobolevDatum s z A → sobolevENorm s z = ‖A‖ₑ。证明是双向不等式，上界取该 datum，下界对每个 datum 用唯一性，不仅是实现里常用的单向 ≤。其 D01 定义与冻结 Data 定义相同的 angular pairing/infimum。
4. 因此在 Ioo 0 S 逐点有 `sobolevENorm 2 (slice w.velocity t) ^ (2:ℝ) = ENNReal.ofReal (‖H t‖ ^ 2)`。右侧由连续 H 的 norm、平方与 ofReal 连续性可测。限制测度 `volume.restrict (Ioo 0 S)` 上，这给出 AEMeasurable；实函数 `‖H t‖²` 为 AEStronglyMeasurable。
5. V4 给出这同一非负函数的有限 lintegral。因此结合第4步、非负性和标准积分转换，可推出 `IntegrableOn (fun t => ‖H t‖²) (Ioo 0 S)`，且其实积分等于下积分的 toReal，得到 B 稿的数值界。
6. 对 B 稿任意只在 Ioo 0 S 表示速度的 G，由第2步 G(t)=H(t)。连续/可测性只需限制在该区间，外部任意值不影响结论。因此 B 的“任意 datum”版本没有额外可测性前件，V4 也没有借用不可测下积分逃避真实 H² 有限性。

**可核验桥的精确状态：** 已存在点态唯一性和精确范数等式的 Lean 源码；本次没有找到或验证一个专门把 V4 lintegral 直接转成“任意 order-2 datum 路径实平方可积”的打包引理。该打包引理若下游需要，可按上面1–6步证明，前件只需现有 w、S≤T、G 的表示条件与有限界；不得再添加 G 可测、H² 时间可积或解在 T 连续的前件。这里缺的是可消费的组合引理及其编译证据，不是数学假设，也不是 V4 陈述缺口。本次接受不以实现证明只用了单向 sobolevENorm 上界为理由，而以上述现有双向范数等式和经典连续路径为理由。

`COMPARISON_165.md` 第2节的协调结论正确。“桥的证明仍是实现义务”宜读作上述组合桥/使用端的义务；点态范数桥实际已有，不应误报为尚无唯一性或尚无精确 norm equality。

## 既有实现的简短 simplifier 审查

本批只组装既有数学，四模块不需要为注册做重构或清理。

- `EnstrophyIdentity.lean`：先对 first derivative L² 路径求导，再 IBP 和 Helmholtz 正交；平移内窗口及解除 clamp 是处理 t=0 双侧导数差异的必要步骤。最终 momentum 展开、norm/pairing 识别和 ring 简明，未发现可删除的数学假设。
- `EnstrophyBounds.lean`：extended-real 小量先转实数 work bound，Young 明确给 CRH1=2。局部连续性提供 IntervalIntegrable，积分微分不等式保留初始梯度。局部 forceSq 连续性与 H2TimeIntegral 的命名 helper 有少量重复，属于跨模块组织偏好，非本批必要清理。
- `SobolevTwo.lean`：weak derivative constructor 得到真正 angular datum，继而 CH2=16；没有以物理图范数代替目标。toReal 使用在已 MemLp 的 SmoothL2Field 上，不构成无限值归零漏洞。系数不锐利不影响普适合同，无需换成 Fourier 最优常数。
- `H2TimeIntegral.lean`：ordinary L²/K 单调性、enstrophy 积分界和 genuine H² bound 的组合，常数32同时覆盖三项。通过有理内端点的可数有向并到 Ioo 0 S 是合法端点处理，且不读取 u(T)。通用下积分引理本身不要求 integrand 可测；这并不代替上节对于论文语义的可测性审计，但也不是实现错误。零初值由同一主定理 simp 得出，恰当。`_hS` 未使用是结论在更宽域仍可成立的松假设，无需改规范。

## 执行与限制

定向读取 V4、两盲稿协调记录、原 Spec、冻结 Data/V3/DatumLemmas、指定 C01 四实现模块，以及 D01/ForceClass、A04/Forcing 的相关证明。仅写本报告。没有编译，也没有实测简化修改；ACCEPT 限于最终结构的陈述与上述源级数学审查。Lean elaboration、绑定精确投影和公理审计仍由后续运行确认。

### 补充：已核实的连续性组合桥

Root 提醒后定向精读 `A04/Continuity.lean:84–110`：`sobolevNormAt_eq` 精确识别实值规范为 datum norm；`continuousOn_sobolevNormAt_of_datumPath` 和 `continuousOn_sobolevNormAt_velocity` 已将上述点态识别与 w.sobolev 组合为实际半开区间范数连续性定理。这进一步确认可测性链条已有直接源码支持。尚未核实的打包步骤仅剩把 V4 有限下积分转换为任意表示路径的实积分可积及相同上界，不能把连续性本身记作待证明缺口。

本次实际按 `Data.lean:643–645` 的类型读取：它直接给一个在整个 Ico 0 T 连续的 G，不只是分别存在的紧子区间路径。因此无需另行可数粘合。对 S=T 只限制到 Ioo 0 T；报告和比较稿均不应声称 G 在 Icc 0 T 连续。COMPARISON 当前“连续的 order-2 datum 路径”结合后文 `(0,S)` 的上下文没有数学错误，可明确补上“在 Ico 0 T 上”以减少歧义，但不是拒收条件。
