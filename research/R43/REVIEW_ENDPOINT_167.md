# 167 R43 最大族终端 H² 积分独立审查

## 当前结论

当前 MaximalEndpoint 两条生产定理源级成立，足以关闭 **G5 的条件式 endpoint gluing**：在已经给定真实最大解族及 C01 吸收小量的情况下，从其严格短时间片得到每个有限 0<S≤Tmax 的 H² 积分界，包括有限等号。

尚待作者完成/确认冻结词汇消费者后作最终 source verdict；未运行 Lean/lake/Git，不能据此报告编译或公理审计通过。

## 论文和范围

`paper/sections/04-whole-space.tex:119–130` 要求独立 ordinary L² 预算 K(S)，以及三项 `CSK(S)² + Cν⁻¹‖∇a‖² + Cν⁻²∫‖f‖²` 的真实 H² 时间积分界，S 可在最大 lifespan 端点。:132 的延拓排除是下一步，不是本引理自己证明的结论。

`research/R43/R43_SPLIT.md` lane165更新已关闭 fixed-horizon C01，明确 G5 是最大族到终端积分，G7 是另一个 critical energy 问题。新模块保留吸收 hsmall 为显式输入，所以不证明 bootstrap 或由临界 force 小量得到 hsmall；它也没有调用 A04 的完整无限 lifespan 结论。A04.Continuation import 提供 canonical squaredHTwoIntegral 词汇，不等于已完成其 Restart/HigherOrderBound 等分析输入。

## 最大族取片与同一预算

`A02.IsMaximalSolution` 与冻结 V2 两者均是：正 maximalLifespanR，且对每个严格短的正 r 存在 ClassicalSolutionR ν a f r，其 velocity 和 pressure **作为总函数**分别等于 u,p。这比 a.e. 兼容强，足以直接改写 integrand，但不提供终点时间的 PDE 正则性。

maximal_h2TimeIntegral 对每个 0<t<S 取 t<r<S，由 S>0 得 ofReal r<ofReal S，再经 hSL 得 r<Tmax；故仅向 hu 请求严格短的 r。t<r 保证 C01 的 closed-right Ioc 0 t 中每个值都处在 w 的合法 Ico 0 r 内。

调用的是已有 C01.h2TimeIntegral_Ioc，直接把同一最终 S 作为预算端点，保留 K(S)、force 积分上限 S 和初始梯度。该 C01 引理本来允许预算 S 大于短解 horizon，它只在 t 以内取速度值、使用全时 force 的预算。这里无需构造 w:S 或证明预算的又一份单调性。hsmall 在 Ico 0 S 上通过 hw 的总函数等式改写；这不要求 w 在 r 之后是解。

所有短片具有同一个有限 RHS，之后调用 C01.lintegral_Ioo_le_of_Ioc 的有理端点可数有向并，得到 Ioo 0 S 的界。无 S<Tmax 强化，没有目标积分有限前件，没有 endpoint velocity 值假设。即便 Tmax=∞ 也覆盖任意有限 S。

## 真实范数与 measurability

目标 D01.sobolevENorm 2 仍为角频率 datum 的规范，不是物理图范数替身；常数32及三个黏性/初值项均沿 C01 原样使用。C01 对每个短经典片已提供实际有限 H² 控制。

虽然通用 lower-integral 并引理可对不可测函数成立，论文语义并不依赖这个弱点：每个 r<Tmax 的经典片有连续 order-2 datum 路径；D01 唯一性及 A04 的精确 norm/continuity 桥使 u 的真实 H² norm 在每个这样的开子区间连续。严格短正有理端点构成 Ioo 0 S 的可数覆盖，故整个开区间可测；有限下积分因此是同一非负规范平方的真实积分有限性。

S=Tmax 时不包括 S。任何0或S单点值改变均不影响该积分。特别不能从此推出 u 在S的连续延拓或 terminal pointwise H² bound；本任务不是166的 TimeLp 代表值兼容性问题，但相同的端点区分仍必需。

## A04消费与最小性

maximal_squaredHTwoIntegral_ne_top 仅展开 A04.squaredHTwoIntegral，并用已存在 enorm_npow_two_eq_rpow_two 转换 ENNReal 自然平方/实指数平方，随后由 finite RHS 得 ≠⊤。没有更换范数或放大假设。

两条生产定理约50行；使用现有 C01 预算和可数并引理，没有重复其证明或引入新抽象。_ha 为与论文输入类一致的松假设，不代表需求更多正则性。没有本lane必要的重构。

## 最终冻结词汇消费者审查：ACCEPT（source-level）

作者已完成 `research/R43/axioms_endpoint167.lean` 和 `ATTEMPTS_ENDPOINT_167.md`，已逐项只读核对。最终源级 ACCEPT；前述“等待消费者”的状态解除，但编译/公理审计仍未执行。

- frozen_maximal_h2TimeIntegral 使用实际 `Contracts.V2.MaximalPartial.IsMaximalSolution`，没有用自定义较强 family predicate 替换。`Bindings.maximalPartial_isMaximalSolution_iff ... .mpr` 的方向正确：把冻结合同假设转为 A02 实现假设，仍是同一 ν,a,f,u,p。
- lifespan 的桥是 A02 lifespan = frozen lifespan；在局部目标 hbound 中 simp 后精确恢复已有 hSL，不借助额外严格不等式。S=Tmax 的等号能力未丢失。
- smallness 的常数是 `Bindings.energyAbsorptionV4.C₁`，不是另一个存在常数；该父值沿注册 A05 常数继承。源码由 definitional equality 接到 A05.gradientL6Const，实际 elaboration 待Luna确认。
- 完整 bound 消费者使用冻结 Data.sobolevENorm、C01冻结 slice/energyBudget/l2Sq，以及 V2 Frobenius gradientSq。已有 gradientSq equality 向 raw derivative-square integral 重写，正是生产定理目标。初值梯度、K(S)、ν⁻¹/ν⁻²与常数32均未掉项。
- 第二消费者通向 A04.squaredHTwoIntegral S u ≠⊤，原假设未增加。它不是 A04 continuation theorem，不能据此报告已证明 maximal lifespan infinite。
- 两个研究消费者 import 生产模块和真实 Bindings；生产模块没有 import 研究稿。没有新增合同或注册条目。
- 四个 #print axioms 目标分别是两条生产定理和两条 frozen消费者；命令存在不代表结果已通过，需随后读取真实输出。

ATTEMPTS 当前准确称只关闭条件式 G5，并将 G7、吸收bootstrap、无条件A04 continuation排除在外。无需要本lane修改的最小性问题。最终结论仅源审查；等待Luna编译后才可追加验证结果。
