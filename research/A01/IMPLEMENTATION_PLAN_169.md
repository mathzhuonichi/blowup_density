# A01 实施方案：H¹ 时间预算与同区间持久性

更新：2026-09-15，lane 169。依据独立 Astra xhigh [审核报告](REVIEW_H1_REFACTOR_169.md)，采用其“修改后接受”的结论。本文件是当前 A01 调度依据；旧 split 的历史估时和推荐顺序由此替代。目标仍是原版 Section 4 与冻结合同，本次只修订方案，没有新增已证结论。

审核归档保持原文，其绝对路径与行号对应审查时的 [A01 源码树](https://github.com/mathzhuonichi/blowup_density/tree/75bfb4ee9986d280377f5a5e2cc4fb484f506a96) 和 [R43 源码树](https://github.com/mathzhuonichi/blowup_density/tree/a32a09df13e90bc740ec547151a56da361619846)。这两个云端快照可用于核对本机路径对应的仓库文件；本地附件和文献不在本次 PR 上传范围。

## 1. 采用的结构与完成标准

保留四个工作包：**H1-local、Persistence、Smooth carrier、Assembly**。前两个是独立的主要 PDE 任务；后两个也包含尚未证明的时间动力学和压力分析，不能按“两个现成通用封装器”估算工作量。

必须区分三个层次：

1. **低阶预算**：只由初值 H¹ 和外力 L¹H¹ 大小给出统一正时间。
2. **同区间构造**：在该时间上，为同一速度、原初值和原外力获得全阶连续路径、时间光滑性和压力。
3. **API horizon**：同一个 horizon 同时满足 `solution`、`regularity`、`horizon_lower_bound`；前两层全部完成后才能装配。

固定一个基准阶（现有入口可取 q=6，即 H⁷）并在其时间上升阶，是当前有用的中间里程碑。它不提供 H¹ 数据球上的统一时间，也不允许对任意各阶时间取下确界后断言其为正。现行 lane 168 已避免经典解能量的构造循环；这次改动修正旧研究依赖，并非修复一个已经实施的循环。

## 2. H1-local 的内部目标

这是待证明的研究规格，尚不新增 Lean 合同或改写 `Horizon.lean`。

- 初值属于 H¹，并在分布意义或既有闭 L² 无散子空间内无散。裸点态 `fderiv` 不适用于一般粗糙 H¹ 初值。
- 首个消费者保持冻结输入 `a ∈ initialClassR`、`MemForceR f`。后者已有各阶光滑路径、全正时间 L¹/L² 有限性以及紧时间区间 H¹ 有界性。Tao 5.4 的数据定义包含有限区间 L∞H¹ 外力，时间预算却只依赖 L¹H¹ 大小；不把 L∞ 大小加入统一预算。推广到仅强可测 L¹H¹ 外力需另补证明。
- 解类为 \(X^1=L^\infty_tH^1_x\cap L^2_tH^2_x\)，另证明强 H¹ 连续性、初值迹、真实 forced mild 方程及完整窗口上的 X¹ 唯一性。
- 外力的 L¹H¹→热流 X¹ 估计由齐次热估计和 Minkowski 得到；禁止用不成立的 L¹⇒L² 外力蕴含。非线性使用 \(PB(u,u)\in L^4_tL^2_x\)，通过 \(T^{1/4}\) 转入 L²L²，再用热估计闭合不动点。

令 \(A=\|a\|_{H^1}\)、\(F_T=\|f\|_{L^1(0,T;H^1)}\)。采用 \(\tau=\nu t\)、\(\widetilde u=\nu^{-1}u\)、\(\widetilde f=\nu^{-2}f\) 后，预算为：

$$
(A+F_T)^4T\le c\nu^3.
$$

相应自然估计为 \(\|u\|_{L^\infty H^1}+\sqrt\nu\,\|u\|_{L^2H^2}\le C(A+F_T)\)。D01 与文献范数比较常数须明确吸收，不能默认范数数值相同。

为控制非齐次 H² 的低频时间积分，当前选用保守实现约定 \(0<T\)、\(\nu T\le1\)；这是本方案的选择，**不是 Tao 5.4 明写的限制**。完成范数桥后，可选形如 \(\delta=\min\{\nu^{-1},c_0\nu^3/(1+2K_{\rm real})^4\}\) 的正下界。这里有限 K 控制的是冻结 API 的初值 H¹ 和**全正时间**外力 L¹H¹ 范数；不要求优化常数。

## 3. 执行顺序与交付边界

| 顺序 | 工作包 / 任务 | 可验收交付 | 尚不能据此宣称 |
| --- | --- | --- | --- |
| 1（本 lane） | 明确内部目标和依赖 | 本方案与旧 split 对齐，冻结规格保持原义 | H¹ 局部定理已证明 |
| 2（立即下一项） | Persistence：完成 lane 168 连续升阶 | 同一实际 witness 的正则化 source 对齐；有限 word 差值终端估计；uniform Cauchy；连续 H(q+2) 极限；初值、降阶及方程同定，T 不缩短 | 固定 q 时间已经是 H¹ 球统一时间；单个 trace 或 TimeLp 结果已给连续全阶塔 |
| 3（可与 2 并行） | H1-local 与低阶 Persistence | §2 的低阶线性/双线性估计、真实存在和完整唯一性；明确证明 H¹ 到现有可用高阶范围的桥 | 改动现有 q≥6 参数即可得到 H¹；两个任务接口已经接通 |
| 4 | Persistence：低阶时间上的全阶塔 | 在 H¹ 预算的同一 T 上构造同一 ordinary L² carrier 的所有连续 realizations，保留原 a/f 和实际方程 | 只有各阶独立存在即可组塔；塔的空间光滑性已给时间光滑 |
| 5 | Smooth carrier | 真实 mild→每阶时间动力学→全部时间导数，包含 t=0 单侧；复用空间代表并补最少的联合光滑/目标 datum 桥 | `OrdinaryForcedTime` 的内部 L² 一次导数已经足够 |
| 6 | Assembly：压力与经典解 | 证明实际 Leray 补场实值、普通光滑、无旋及 L²；径向势、联合压力光滑、t=0 梯度恢复、momentum、原 a/f 同定 | `PressureGauge` 或分布压力已经生成所需普通压力 |
| 7 | Assembly：完整 LocalTheoryAPI | 在低阶预算上同时给 horizon、solution、regularity、horizon_lower_bound | 单独 H¹ mild 时间已完成 API 下界字段 |
| 8 | A02 / A04 / R43 后续 | 真实统一重启、重叠拼接、最大族路径与端点延拓；保留各节点独立前件 | A01 四包完成自动证明所有继续性和临界估计 |

### 立即下一项：保留并消费 lane 168

复用 `ForcedMaximalRegularity`、`ForcedSourceUpgrade`、`HeatGradientTrace`。实际 source 及其 a.e. 降阶、标量终端梯度能量/耗散估计已证明；下一项从**正则化差值与该实际 source 的对齐**开始，继而有限 word 求和、uniform Cauchy 和连续路径完备化。TimeLp/a.e. 收敛本身不给端点迹。

从 lane 166 的完整存在结论**只取一次 witness**，在同一 witness 上使用 lane 168 的 source 构造；保留范数、无散、角不变性、原始数据、外力和 mild 方程。不能分别取两个存在见证再默认相等。全过程按真实前件复用有限阶工具，不以要求 `ClassicalSolutionR` 的能量定理构造该结构。

### 低阶持久性须单独闭合

当前 actual-source / transport 入口要求 q≥6 / s≥6。方案保留两种可评估的证明路线，选定后再分配实现，不把任选一路写成已证输入：

- 真正的 X¹→X² bootstrap（文献可经 s<3/2，例如 5/4），再补 H²→H⁷ 的非线性和时间类适配，接高阶 trace 链。
- 光滑高阶近似或短时高阶解上的 tame 持久性，由固定低阶解控制，并用真实唯一性延展、同定到同一 H¹ 时间。

现有 A03 m≥2 datum 乘积可复用；它不自动解决低阶完成空间、Bochner 时间类和 cylinder/ordinary 适配。

## 4. 兼容、时间和压力的明确输入

**跨阶兼容先于唯一性。** 核对同一 a/f、t=0 迹、Leray/非线性/heat/kernel/convolution 降阶、连续线性映射穿过积分、时间平移与窗口、ordinary/cylinder 和角不变性。再证明比较对象确属 X¹，并处理完整窗口唯一性。现有 Volterra 定理的球界、Lipschitz 和 `kernelMass * L < 1` 前件仍须满足；`ContinuationInvariant` 不是现成 H¹ 唯一性。

**塔与时间分开。** 复用 `EulerOrdinarySobolev.SobolevTower` 的 field、realization、value_eq。若各 lift 已共享同一 ordinary L² carrier，用 `value_injective` 同定，不新增重复的两两兼容结构。全阶连续空间路径仅给空间光滑和连续 jets；实际 PDE 的时间 bootstrap 仍是独立证明。`ProjectedEquation.projected_of_classicalSolution` 在经典解装配后填字段；前置动力学必须来自实际 mild 方程。E1 的纯演算恒等式可在已有可微性时复用，与上述需要经典解的定理区别处理。

**压力使用真实补场。** 取 \(G=(I-P)(f-\operatorname{div}(u\otimes u))\)，先证普通 G 的光滑、对称 Jacobian / 无旋性和 L²，再用 `RadialPotential`。HeliCorgi 的分布结论是 \(\nabla p=-(I-P)F\)，故使用 F=advection−f 或对应负号，并补复值/实值、分布/普通场运输。压力须在所需区间联合光滑，梯度满足 L² 与初始端点身份，最后装 momentum 和 gauge。不要求全空间标量 p∈Hm。

## 5. 继续性与保留模块

- H² 平方时间积分→H¹ 有界→统一 H¹ 重启是目标路线。先评估已有 m=3 Grönwall 再降阶 H¹ 的消费者，并补同一实际最大解族的 `hpath`、有界性和端点拼接。这只处理该解的继续性，不能替代 H¹ 数据球统一局部定理。
- `GronwallInstance` / `HighContinuationIntegral` 的 m≥3 前件保持；若以后需要 m=1 能量入口，先独立证明，零范数处须用正则化避免除零。冻结 `HigherOrderBound` 的所有自然阶义务保持，即使重启只消费 m=1。
- 当前 `MemForceR` 已有全正时间 L¹/L²；复用 `forceSobolevENormL1_timeShift_le` 与 `MemL1Hm` 给统一未来尾部帽，当前 Section 4 数据类无需新增 cutoff。仅在研究更广的紧区间光滑外力类时，才另需局部范数重启或 cutoff 及同定；冻结 A01 Spec 已明确收窄范围。
- 平行 [PR #168](https://github.com/mathzhuonichi/blowup_density/pull/168) 的 R43 G5 给真实最大族的端点 H² 积分（S≤Tmax，含等号），仍需 `hsmall`。该证明位于另一分支；A05 / R43 G7 与 A04 无条件延拓仍开。保留低频能量和外力 L² 项。
- 保留 `OrdinaryForcedLocal` 高阶入口、`ContinuationInvariant` 窗口机制、`Horizon.horizonOf` / `HasAprioriBound` 给定 S 的辅助用途、全阶 Grönwall、纯空间范数桥、既有 tower、source/trace、压力 gauge。`AprioriRows` / `SliceWiring` 的 classical 消费者只在其前件已构造后使用。

## 6. 调度与记录

lane 169 只更新方案与审核归档；下一全局 lane 为 170，首选 §3 第 2 项。可另开一条第 3 项的低阶供给研究，与连续升阶并行；每次都明确独立交付及未证输入。

代码交 Astra low subagent；所有 Lean 编译、合同和变异测试交 Luna high subagent。主 agent 负责文档、云端对齐和 worktree/PR。沿当前 A01 PR 链提交，不把另一分支的结果记为本树已包含，也不以本地成功代替云端 CI 成功。
