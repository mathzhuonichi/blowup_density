# C01 独立盲稿 A

## 1. 陈述范围

本稿只读取原论文、CLAUDE.md、冻结的 Contracts/V1/Data、V1/GradientL6、V1/V2/V3/EnergyAbsorptionPartial；未读取 formalization 实现、research/C01/Spec.lean、其他 C01 草稿或会话记录。冻结合同的注释自带旧 Spec 引文，这些仅随父接口读取，未据其推导新字段。

`EnergyAbsorptionFullAPI extends EnergyAbsorptionPartialV3API` 原样保留全部祖先字段。新增 enstrophy identity、局部吸收微分界、积分界、含终端时刻的 Laplacian 时间积分界、实际角频率 H² Fourier 界、一般及零初值 H² 时间积分界。这里只定义合同结构，不声明或假设存在实例。

不包含两个临界半阶微分估计、连续性 bootstrap、Grönwall、全局存在、延拓或最大寿命定理；这些是 §4.3/4.4 调用本接口的下游论证。

## 2. 逐项来源与推导

- 普通能量：04-whole-space.tex:117–120 的独立普通能量恒等式和 eq:RL2；02-preliminaries.tex:136–149 显示倍数 1/2、耗散 ν、正则化范数除法。V3 已完整继承这些字段，不重写。
- Enstrophy identity：04-whole-space.tex:106–115 明确测试 -Δu。若 E = ||∇u||²，N = <(u·∇)u,Δu>，则 E' = -2ν||Δu||² + 2N - 2<f,Δu>。压力项由 solenoidality 消去；不是新前件。
- 吸收：04-whole-space.tex:108–112 的三因子 Hölder 和导数嵌入。父合同 C₁ 的读法是乘 ||u||₃，而论文第110行写的是已经嵌入后的 C₁y；故新前件使用父接口的 C₁||u||₃ ≤ ν/4，而不是误将同一常数直接乘 y。第171行正是 §4.4 的 ||u||₃ 小量入口。
- Young：在上述前件下，2|N| ≤ (ν/2)||Δu||²，且 2||f||₂||Δu||₂ ≤ (ν/2)||Δu||² + 2ν⁻¹||f||₂²，故 CRH1 可以全局取 2，得到第114–115行的精确 ν 次幂。对 [0,t] 积分保留末端梯度项；丢掉该非负项再除 ν，得到 ν⁻¹||∇a||² + CRH1 ν⁻²∫||f||²。
- 终端：04-whole-space.tex:121 指明 S 可以在最大寿命处，第127–130行正需要这种情况。先取 t<S 的积分估计，再用单调收敛，得到开区间 (0,S) 的耗散界。草稿 `0 ≤ S ∧ S ≤ T` 包含 S=T 与空区间 S=0，绝不评价 u(T)。有末端梯度值的积分界则只允许 t<T。
- Fourier：04-whole-space.tex:123；实际 `Data.sobolevENorm 2` 使用角频率 datum，而非把 H² 定义成 L²+Δ 的图范数。由 (1+r²)² ≤ 2(1+r⁴) 可选 CH2=2；向量平方范数为分量平方和。Appendix B:8–9 固定 Λ 的角频率符号；:22–24、:96–103 覆盖向量及张量；:109–110 要求全局常数。
- H² 汇总：第119、127–130行，利用 K(t)≤K(S)，得 CH2 S K(S)² + CH2 ν⁻¹||∇a||² + CH2 CRH1 ν⁻²∫||f||²。可全局选 Cassembly=4（配合上述 2、2）；结构只要求存在固定正数满足所有字段，不把特定数值作为规范负担。零初值消去梯度与初始 L² 项，对应第171行。
- 正则性由原定义提供：02-preliminaries.tex:12–24 的 H∞ 初值与 F_R、:29–30 的时间连续性；Data.lean:624–648 的 ClassicalSolutionR 字段。无需附加时间导数、PDE 可微、积分收敛、压力额外衰减、紧支撑、jet 正则性等假设。Appendix A:127–144 解释同类能量测试与 Fourier 近似正当性；延拓本身在 02-preliminaries.tex:104–115，留给下游。

## 3. 论文与规范定义的张力

1. 父合同 C₁ 与论文第110行同名但数学因子不同，已通过 L³ 前件明确区分；下游必须先做半阶到 L³ 嵌入。
2. ClassicalSolutionR 仅覆盖 [0,T)，其总函数在 T 处无约束。因此不能把带 u(t) 的结论拓宽为 t≤T；时间积分可涵盖 S=T，因为端点为零测集。
3. `l2Sq`、`laplacianSq`、`pairing` 是继承的实 Bochner 积分，脱离 H∞ 类可能 totalize。这里没有扩大数据类；有界性、可测性与积分正当性须从已有类证明。H² 左边使用 ENNReal 的实际 Sobolev 范数下积分，右边 ofReal 是有限实数，因而界本身同时排除无穷。其与真正 Bochner H² 时间平方范数一致所需可测性由经典解连续 datum 路径推出，不能靠额外前件跳过。
4. 定义只有压力梯度 L² 和真实 PDE，没有逐字存储 Leray pressure 公式；能量证明应由这些定义推出压力消去，不要求 p∈L²。
5. 微分不等式字段允许输入 E'，但 enstrophyIdentity 同时无条件提供真实 HasDerivAt，故没有将导数存在转嫁给调用者。

## 4. 验证

按分工没有运行 Lean 或 lake；草稿语法与类型尚待 Luna high 编译。未写证明、未引入占位证明或存在断言，未修改 Contracts、全局记录，也未 commit/push。只产出 BLIND165_A.lean 与本说明。

## 编译反馈后的纯语法修复

Luna 的首次 typecheck 失败（日志 tmp/probe_165_BLIND165_A.log）：ν⁻² 不是有效 Lean 记号。按 root 反馈，仅将其改写为 (ν⁻¹) ^ 2；数学内容、字段与独立盲稿形成过程不变。本代理未运行编译，修复后结果待编译者确认。
