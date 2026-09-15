# A01：H¹ 基础定理重构建议的独立审核

日期：2026-09-15。审查方式：Astra / xhigh 独立源码与本地文献审核。

## 总评

**修改后接受数学架构方向；不接受立即按原建议整体重构，也不接受其工作量压缩判断。** 以低阶局部时间控制同区间高阶持久性，最终构造一个普通光滑载体，符合冻结稿的数学目标。但是，“唯一新增核心定理”“跨阶兼容自动得到”“压力直接复用”“Assembly 主要只是封装”均掩盖了尚未证明的输入。

当前最有价值的调整是：明确区分低阶时间预算、同区间正则性、经典解/API 装配三个证明层次。**不能把尚未装配的经典解 horizon 直接替换为一个 H¹ mild 时间，然后宣布 `horizon_lower_bound` 已完成。** 也不应为了这种架构，丢弃最新同区间 source/trace 工作或重写已经存在的 Sobolev tower。

最新路线没有实施原建议所批评的经典解循环。`PERSISTENCE_ROUTE_168.md:29–45` 明确禁止用 `AprioriRows` / `GronwallInstance` 的经典解前件构造经典解；`Horizon.lean:61–66` 已明确指出高阶 Grönwall 不提供 H¹ horizon 下界。旧研究表里可能仍有需要整理的依赖描述，但这不能当作当前证明循环的证据。

本报告仅提出审核结论和后续建议；**没有调整计划、合同、Lean 源码或 Git 状态，没有运行 Lean 或编译，也没有宣称渲染 QA**。

## 1. 审查对象与证据边界

- 原建议全文：[pasted-text.txt](C:/Users/zchi/.codex/attachments/21aedd67-1122-4f52-9f81-4727b1115c19/pasted-text.txt)。下文“建议 1–8”“停止路线 1–7”“四个工作包”均对应该文件。
- A01 源码：`C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence`，实际核对 HEAD 为 `75bfb4ee9986d280377f5a5e2cc4fb484f506a96`。
- R43 源码：`C:/Users/zchi/Documents/ChatGPT/blowup-trees/167-r43-endpoint`，实际核对 HEAD 为 `a32a09df13e90bc740ec547151a56da361619846`。该分支的最新端点结果不能冒充已经进入 A01 树。
- 目标为上述 A01 树中的原版 [Appendix A](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/paper/sections/appendix-a-local-theory.tex:60)、[Section 4](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/paper/sections/04-whole-space.tex:1) 和 [A01 Spec](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/research/A01/Spec.lean:277)。没有把主目录的 revision 文稿当作新的形式化目标。
- 当前状态实际读自 [NEXT_SESSION.md](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/NEXT_SESSION.md:3) 和 [PERSISTENCE_ROUTE_168.md](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/research/A01/PERSISTENCE_ROUTE_168.md:1)。本报告的“已有定理”指当前源码有相应证明体；已有编译/公理审核状态仅转述该树记录，未独立重跑。

### 本地参考资料核实

| 资料 | 实际内容与可用范围 |
| --- | --- |
| [Tao 2013 发表版](C:/Users/zchi/Documents/ChatGPT/blowup_density/reference/Tao_2013_Localisation_Compactness_Published.pdf) | 有完整正文。核对发表页 29、31、35–40、48–54；发表页码与 PDF 页码相差 23，例如发表页 52 是 PDF 第 29 页。核心依据是 H¹ data 定义、式 (13)、Lemma 2.1、Theorems 5.1/5.4。 |
| [Tao 2018 讲义](C:/Users/zchi/Documents/ChatGPT/blowup_density/reference/Tao_2018_Local_Wellposedness.html) | 是实际讲义正文，含公式。Corollary 40 附近给出从所有空间 Sobolev 阶到所有时间导数的 bootstrap；Euclidean discussion / Exercise 48 附近讨论经典解压力规范化。该讲义对应段落主要处理无外力方程，不能单独替代带外力 H¹ 定理的规格。 |
| [Fujita–Kato 1964 HTML](C:/Users/zchi/Documents/ChatGPT/blowup_density/reference/Fujita_Kato_1964.html) | **只有 Springer 订阅预览、书目信息和参考文献，没有论文证明正文。** 文件存在不等于所需文献正文已保存。可作为历史书目，不能据此断言已核对某个强迫范数或定理。 |
| [Taylor PDE III Chapter 13](C:/Users/zchi/Documents/ChatGPT/blowup_density/reference/Taylor_PDE_III_Chapter13_Author.pdf) | 有实际章节正文，共 96 页。章节页 5，Propositions 2.3/2.4 支持 Sobolev 嵌入；页 10–11，Propositions 3.6/3.7 支持乘积与交换子估计。它们不直接给出建议中的 Lean 全阶联合光滑封装器。 |

PDF 采用只读文本提取；未下载文献，未生成或检查页面渲染。公式歧义处结合定义与相邻证明核对，没有把抽取中的排版错位照搬成数学结论。

## 2. Tao 5.4 的准确规格：必须先修正的四点

### 2.1 范数、数据类与唯一性类不同

Tao 发表页 31 的 H¹ data 定义包含：初值属于 H¹ 且分布意义无散；外力属于有限区间上的 \(L^\infty_tH^1_x\)。发表页 52，式 (46) 控制局部存在时间的却是 \((\|a\|_{H^1}+\|f\|_{L^1(0,T;H^1)})^4T\)。二者不能混写。

对冻结 A01 的实际输入，这不构成额外障碍：`MemForceR` 给每阶光滑 Sobolev 外力路径以及全正时间 L¹/L² 有限性；[A04/Forcing.lean:140](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A04/Forcing.lean:140) 与 [:160](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A04/Forcing.lean:160) 已分别给出 `MemL1Hm` 和任意紧时间区间的 H¹ 有界性。**H¹ 球上的统一时间仍应只依赖初值 H¹ 和外力 L¹H¹ 范数，而不是额外依赖外力 L∞ 的大小。** 若把基础定理扩大为只假设强可测 L¹H¹ 外力，这是可以研究的加强版，但应补证明，不能称其为 Tao 定理原文。

发表页 37，式 (13) 的 \(X^1=L^\infty_tH^1_x\cap L^2_tH^2_x\)，交空间范数取两项之和。Theorem 5.4(i) 再给强 H¹ 连续性。唯一性 (iii) 的输入是满足真正 mild 方程的这个解类；单独的 `ContinuousH1Path`、连续 L² 路径或任意高阶代表并不是完整的唯一性输入。若新定理真的量化粗糙 H¹ 初值，不能用裸 `fderiv` 定义的普通点态 `IsSolenoidal` 代替分布无散或已有闭 L² 无散子空间；冻结稿的光滑初值可通过现有桥进入该空间。

### 2.2 黏性缩放

令 \(A=\|a\|_{H^1}\)、\(F_T=\|f\|_{L^1(0,T;H^1)}\)。冻结 Appendix A:79–87 的变换是 \(\tau=\nu t\)、\(\widetilde u=\nu^{-1}u\)、\(\widetilde f=\nu^{-2}f\)。因此缩放后的初值范数为 \(\nu^{-1}A\)，外力时间积分范数为 \(\nu^{-1}F_T\)，时间为 \(\nu T\)。式 (46) 变为：

$$
(A+F_T)^4T\le c\nu^3.
$$

在相同归一化及下面的短时间约定下，对应的自然解估计为 \(\|u\|_{L^\infty H^1}+\sqrt\nu\,\|u\|_{L^2H^2}\le C(A+F_T)\)。D01 与文献 Sobolev 范数的归一化比较常数应吸收进 \(c,C\)，不能默认为数值完全相等。原建议已允许稍后确定黏性次数，故这里是补全其伪码，不能把未定义的 `c ν` 武断解释为已写错的线性黏性常数。

### 2.3 时间区间及小时间上限

**实际核对的 Theorem 5.4(ii) 正文没有明写 \(T\le1\)**；发表页 35 的常数约定为无下标的隐常数绝对、依赖参数须用下标表示。发表页 31 的时间条件为 \(0<T<\infty\)，页 35–40 没有发现把整节统一限制为 \(T\le1\) 的约定。因此不能声称“Tao 明确要求 T≤1”。

但是，不能由此在 Lean 中无核查地采用长区间、时间无关常数的非齐次热流估计。式 (13) 使用完整 H²，含低频 L² 部分；对 Fourier 支持在 \(|\xi|\ll T^{-1/2}\) 的初值，自由热流的该时间 L² 部分可达 \(\sqrt T\|a\|_2\)。所以实现引用 Lemma 2.1 的标准局部估计时，须明确限制区间长度，或保留真实的时间依赖。

**本审核建议的保守实现规格**是加 \(0<T\) 与 \(\nu T\le1\)，不把它误报为原文限制，也不在本次审核中扩大为整篇文献纠错。此限制不损害冻结稿要求的正统一局部时间。经范数常数吸收后，可取类似 \(\delta=\min\{\nu^{-1},c_0\nu^3/(1+2K_{\rm real})^4\}\) 的正下界；这只是可用的选择，不是要求现在变更 API 或追求最优常数。

### 2.4 L¹ 外力怎样产生 L²H² 解控制

不是由 \(f\in L^1H^1\Rightarrow f\in L^2H^1\) 得到——这个蕴含不成立。Tao Lemma 2.1，发表页 39–40，式 (21) 是齐次热估计加 Minkowski：逐个注入时刻的 H¹ 数据各自产生可控的热轨道，再对外力的 H¹ 大小作时间 L¹ 积分。连续 H¹ 迹还需相应 Duhamel 连续性论证。

非线性则由式 (24)/(25) 给出 \(PB(u,u)\in L^4_tL^2_x\)，继而以 \(T^{1/4}\) 因子进入 \(L^2_tL^2_x\)，用式 (22) 控制 X¹；这才是定量不动点的低阶机制。**现有 `viscous_mild_maximal_regularity` 需要连续 Hq source，并不已经提供这个混合 L¹ 外力/X¹ 非线性基础定理。**

## 3. 建议 1–8 的决定矩阵

| 项 | 决定 | 数学与当前 Lean 证据、必要修订 |
| --- | --- | --- |
| 1. 单独形式化 forced H¹ local theorem | **修改后接受** | 数学依据充分：Tao 5.4(i)–(iii)，发表页 52；精确修订见 §2。拒绝“唯一需要新增的核心 PDE 构造”：低阶 X¹ 双线性/热估计、唯一性窗口化以及 persistence 都是真实分析。当前 [OrdinaryForcedLocal:32](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Source/OrdinaryForcedLocal.lean:32) 要求 `6 ≤ q`，输出 H(q+1) 连续路径和普通 L² 下降，不能改参数就得到 H¹。 |
| 2. horizon 下界直接依赖 H¹ 定理 | **修改后接受** | 接受“先选低阶定量时间，再在该时间上证明持久性”的数学顺序；拒绝“H¹ mild 存在立刻给当前 API 的 horizon 下界”。[Spec:283–307](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/research/A01/Spec.lean:283) 的同一个 horizon 还必须携带 `ClassicalSolutionR` 和所有 regularity 字段。应先证明低阶预算的统一性，完成同区间经典构造后，才将这个预算装成 API horizon 并得到 :338 字段。[Horizon:50–66](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/Horizon.lean:50) 已承认这点；其 `horizonOf` 是给定 S 的辅助量，不宜原地改写。 |
| 3. 单一参数化 persistence theorem | **修改后接受** | 同 T、同解的结论是正确目标，Tao 5.4(ii)/(iv) 支持。拒绝把 `C Hm → L² H(m+1) → C H(m+1)` 当作自动迭代；第二箭头还需高初值迹和足够高的实际 source。详见 §4。现有工作是可保留的高阶段供应，不覆盖 H¹ 起步。 |
| 4. 唯一性自动给跨阶兼容 | **修改后接受** | 唯一性是合适的方法，但“自动”“不需要比较理论”不成立。必须先证明降阶后的方程真是同一个方程，以及两个对象处于 X¹ 唯一性类。现有 [VolterraUniqueness:22–31](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/vendor/NavierStokesAndEuler/Euler/VolterraUniqueness.lean:22) 明确要求球界、Lipschitz 界和 `kernelMass * L < 1`；[ContinuationInvariant:69–100](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:69) 是高阶角不变性窗口机制，不是现成全 X¹ 唯一性。完整的 restriction 输入见 §5。 |
| 5. 新增全阶路径到普通联合光滑场封装器 | **修改后接受；拒绝重复造 tower** | [OrdinarySobolevTower:23–69](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/vendor/NavierStokesAndEuler/Euler/OrdinarySobolevTower.lean:23) 已有同一 ordinary L² 场、全阶连续 realizations、光滑空间代表、连续 L² jets 和 realization 同定。新增应只补已给定时间光滑路径的联合光滑/目标 datum 适配部分。建议伪码的 `hsmooth` 是重大输入，不能由 tower 的连续性白得；\(u(t,x)=g(t)\phi(x)\) 中连续不可微的 g 就说明空间全阶不足。Taylor Ch.13 的嵌入/乘积定理支持工具层，不是这个联合时间结论的现成定理。 |
| 6. 空间全阶后统一证明时间光滑 | **接受，实施须明确前件** | 顺序正确，正是冻结 Appendix A:71–76 与 Tao 2018 Corollary 40 附近的论证。先用真实 mild 方程获得每阶的积分/导数身份，再对右端 bootstrap；不是先调用已经假设经典解的 `ProjectedEquation`。现有 [OrdinaryForcedTime:36–58](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Source/OrdinaryForcedTime.lean:36) 只给内部时间 ordinary L² 导数，尚须高阶搬运、全部时间导数和 t=0 单侧版本。 |
| 7. 速度完成后恢复压力 | **修改后接受** | 径向势方向与冻结稿一致；局部速度构造无需同时选择 scalar pressure。但是不能“直接复用”现有压力结论来省掉从 Leray 补场到普通光滑无旋场的桥。还须证明 p 联合光滑、梯度 L²、t=0 恢复和 momentum，且 HeliCorgi 梯度定理的符号为负。详见 §6。 |
| 8. H² 准则作为 H¹ 重启推论 | **修改后接受；暂不优先新增 m=1 能量入口** | 数学方向正确；当前 [Continuation:197–219](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A04/Continuation.lean:197) 已只消费 `HigherOrderBound` 的 m=1 实例来重启。可是 [GronwallInstance:68–78](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/GronwallInstance.lean:68) 与 [HighContinuationIntegral:85–101](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A04/HighContinuationIntegral.lean:85) 仍要求 m≥3，不能直接实例化 m=1。短期先考虑 m=3 界再降阶 H¹；这只处理某个解的继续性，不给整个 H¹ 数据球统一局部时间。冻结高阶合同也不能因此删除。 |

## 4. Persistence 是独立的主要 PDE 任务

### 4.1 最新供应的确切强度

1. [ForcedMaximalRegularity:30–42](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/ForcedMaximalRegularity.lean:30) 从实际 forced mild 路径得到同 T 的 `TimeLp H(q+2)`、a.e. 降阶及平方范数可积。它没有输出连续 H(q+2) 路径。
2. 底层 [SobolevMaximalRegularity:45–56](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/vendor/NavierStokesAndEuler/Euler/SobolevMaximalRegularity.lean:45) 对任意自然 q 给线性 maximal regularity，但前件是连续 Hq source、连续 H(q+1) 解和真实 heat/Duhamel 方程；不能据“任意 q”省去低阶非线性映射及 source 时间类。
3. [ForcedSourceUpgrade:22–80](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/ForcedSourceUpgrade.lean:22) 已构造真实 \(P(f-\operatorname{advection}(u,W))\) 的 `TimeLp H(q+1)`，证明 Leray、forcePath、transport 的相容性，且同原 source a.e. 相等。这正是建议 4 不可跳过的实际证明，不是冗余装配。
4. [HeatGradientTrace:13–22](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/HeatGradientTrace.lean:13) 与 [:52–64](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/HeatGradientTrace.lean:52) 保留终端梯度能量及耗散。这是实质进展；但其输入为连续 H³ 路径、连续 H¹ source 及逐方向实际热方程导数。不能把一个粗糙 TimeLp source 直接塞进去。

因此，当前下一步“实际正则化 source 对齐 → 有限 word 差值的统一 trace/Cauchy 界 → 连续高阶空间完备化 → 降阶同定”仍合理。单个终端估计尚未完成这条链；仅有 a.e. 或时间 L² 收敛不保证 t=0/T 的迹，也不保证 uniform convergence。

### 4.2 H¹ 到现有高阶供应之间缺什么

Tao 5.1(iv) 的证明并不是只写一句整数归纳。发表页 49–50 先用 \(PB(u,u)\in L^4L^2\) 和线性式 (23) 升到 \(X^s\)、\(s<3/2\)；例如选 s=5/4 后，用相应的 L¹² / L^(12/5) 空间控制非线性的一阶导数，获得 \(PB(u,u)\in L^2H^1\)，再到 X²。之后才继续高阶迭代。5.4 在发表页 53 明确重复该证明；5.1(ii) 的高阶估计论证则留给读者，不能当作已经形式化的单行调用。

现有 `AsymmetricTransport` / `TimeSobolevTransport` 的主要映射要求 s≥6；A01 的 actual-source 入口要求 q≥6。因此新的 H¹ 定理并不会自动接上 lane 168。须选择并完成以下之一：

- 形式化真正低阶 X¹/X² bootstrap，再把 H² 至 H⁷ 的非线性、时间类和相容性补齐，接入既有高阶 trace 链；
- 或对光滑高阶近似/短时高阶解证明由低阶解控制的 tame 持久性，并用已证明的唯一性将其延展、同定到固定 H¹ 时间。

这里并非所有乘积工具都缺失：[A03/RealAngularProduct:150、215](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A03/RealAngularProduct.lean:215) 已有 m≥2 的真实 Sobolev datum 乘积；[OuterTameProduct:177](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A03/OuterTameProduct.lean:177) 有有限阶外积估计。这些值得复用。但低阶完成空间、时间积分与 cylinder/ordinary carrier 的适配仍须证明，不能因为库中某处有 H² 乘积就称桥已经闭合。

**长期推荐**是 H¹ 时间 → 同解持久性。**当前最窄的可执行下一步**仍是完成 lane 168 的连续升阶；它能把固定 q 的结果提升为固定基准阶时间上的全阶载体，但还不能解决 H¹ 球上的统一 horizon。两者应在计划中分别标明，不以重构名义混为一个已接通的任务。

## 5. 跨阶兼容：唯一性之前的必要条件

调用唯一性之前，至少要核对：

- 初值 restriction 确为同一 a，包含 t=0 迹；外力路径在降阶后仍为原 f，而非临时 surrogate。
- Leray 投影与降阶可交换；高低阶非线性是同一个物理输运项。现有 [SobolevNonlinearCompatibility:23–42](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/vendor/NavierStokesAndEuler/Euler/SobolevNonlinearCompatibility.lean:23)、[CorrectionSourceRestriction:19](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/vendor/NavierStokesAndEuler/Euler/CorrectionSourceRestriction.lean:19) 和 `ForcedSourceUpgrade:16、53、77` 提供不同层次的桥；其阶数与 source 前件不能省略。
- heat operator、heat kernel、卷积与 restriction 可交换；积分可积性和连续线性映射穿过积分须成立。[MildEquationBridge:17–64](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/vendor/NavierStokesAndEuler/Euler/MildEquationBridge.lean:17) 有相关供给，但不是任意非线性 mild 方程的自动比较定理。
- 时间窗口、timeShift、force restriction、原始起点和普通/cylinder 实现一致。高阶角不变性必须保留，否则 cylinder 对象未必对应 R³ 普通场。
- 两个待比较对象确属 X¹，且有完整时间窗口唯一性。`C H1` 自身不包含 `L² H2`；m=0 的路径尤其不能单凭其阶数被视为 H¹ 解。`TimeLp` 的 a.e. 等式最终须提升为连续路径的每点等式，才能给出初值和终点同定。

也不必机械地为每一对阶数另建一个全局唯一性理论。若 persistence 直接构造“同一个 low path 的连续高阶 lift”，则各 lift 共享 ordinary L² 值，现有 `value_injective` 等工具可以得到兼容性。`OrdinarySobolevTower` 实际只要求 `field`、`realization` 和同一 `value_eq`（:23–26），没有要求用户再提交一套重复的两两比较数据。应选使输入最少的路线，但不能省掉真实方程同定。

## 6. 光滑载体和压力仍需完成的桥

### 6.1 复用 tower，补时间与目标空间适配

现有 tower 输出每个时刻的 `SmoothL2Field` 和连续 jets，已覆盖建议 5 的大量空间代表工作。仍须把 Sobolev 时间路径的高阶导数通过连续线性空间导数/evaluation 搬运为混合导数，再证明 `(t,x)` 联合光滑。全阶时间 `ContDiffOn` 是建议 6 的 PDE 工作输出，不是纯 Sobolev 嵌入输入自动产生的东西。

还需显式照顾冻结目标 `[0,T)` 的单侧初始时间。`OrdinaryForcedTime` 当前导数是 `Ioo 0 T` 上的 `HasDerivAt`；`Spec.sobolev_smooth` 则是 `Ico 0 T` 上的 `ContDiffOn`。如果改用 `[0,T]` 的中间强定理，应证明其限制满足目标，并避免把负时间任意延拓的双侧导数当成初值单侧导数。

### 6.2 压力恢复的正确方向

令 \(w=f-\nabla\cdot(u\otimes u)\)，目标为 \(G=(I-P)w\)、\(\nabla p=G\)。现有 [RadialPotential:138](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/RadialPotential.lean:138) 和 [:223](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/RadialPotential.lean:223) 可以在 **G 已光滑且 Jacobian 对称** 后证明径向势梯度等于 G。缺口不在势积分公式本身，而是证明实际 Leray 补场具有这些前件、属于 L²、随时间联合光滑，并恢复原 momentum。

HeliCorgi [R3HelmholtzPressure:252–263](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:252) 的结论是 \(\nabla p=-(I-P)F\)，且位于复值 tempered distributions。若引用它，须取 \(F=\nabla\cdot(u\otimes u)-f\) 或取压力负号，并补实结构、普通代表及分布到点态的桥；不能直接把 F=w 套进去。它可支持分布 curl-free 论证，但并不已经是 `HasSymmetricJacobian G`。现有 `D01/Longitudinal` 的主方向是“已知无旋 → Fourier longitudinal”，逆向也不能省略。

[PressureGauge:167](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/PressureGauge.lean:167) 与 [:200](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/PressureGauge.lean:200) 主要处理已有压力与其自身梯度径向势的 gauge。它不是从任意 Leray residual 一步构造完整经典压力。

[ProjectedEquation:40](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/ProjectedEquation.lean:40) 的输入已经是 `ClassicalSolutionR`；它只能在构造完成后填 `ManuscriptLocalRegularity.projected`。构造前须从真正 mild 方程得到投影演化，再与径向势梯度、convection/advection 恒等式组合得到 momentum。若反过来用该定理提供构造或时间 bootstrap 的演化方程，才会引入当前路线明确避免的循环。

无需要求 whole-space scalar p 属于所有 Hm。一般外力的逆散度势具有低频问题，而目标仅要求光滑 scalar 代表和 L² 梯度；径向势规范可直接满足这一路线。不能把 Tao 对某些规范化压力的全局 Sobolev 叙述不加条件搬给任意当前 force。

## 7. H² 继续性：推荐数学简化与最省当前工作的区别

### 7.1 新 m=1 能量论证不是现成实例

建议中的微分不等式数学上合理，但不能直接以裸 \((\|u\|_{H^1})'\) 作为处处存在的前提；零范数时须正则化。现有 [A04/Regularized:65、134](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A04/Regularized.lean:134) 可复用正则化平方根和积分不等式的实分析核心，而真正 m=1 的 PDE 配对、输运估计、压力消去与 norm/datum 桥仍需提供。[HighContinuation:131–159](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A04/HighContinuation.lean:131) 和原稿 Appendix A:129–145 目前均在 m≥3 工作。

对已存在的单个经典解及其最大族，可以先用 m=3 的既有估计，在统一 H² 积分帽下得到 H³ 界，再通过 Sobolev 降阶控制 H¹。标量降阶范数供应见 [RealAngularProduct:198](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A03/RealAngularProduct.lean:198)，向量 datum/范数还须相应搬运。这条路线依然需要 `HasSmoothSobolevPath` 的供应与最大族同定；不能说当前已经无条件完成。

该替代减少了新增 m=1 PDE 证明的迫切性，**但完全不能从 H³ 数据大小推出整个 H¹ 数据球的统一 δ**。后者仍必须来自真正 H¹ 局部定理。应严格隔离这两个用途。

### 7.2 外力和端点

冻结 `Spec.horizon_lower_bound:338–343` 的 `forceSobolevENormL1 1 f` 是全正时间范数，不是某个未知局部 horizon 的积分。当前 [A04/Continuation:170–182](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A04/Continuation.lean:170) 已复用 `forceSobolevENormL1_timeShift_le` 处理非负 timeShift 的全局 L¹ 尾部界，且 `MemForceR` 已保证该全局范数有限。因此 Section 4 冻结数据类内无需为此新增 cutoff。

如果讨论原 Proposition 的更广“只在各紧区间光滑”的外力类，单有 `[0,S+1]` 上的有界性并不保证全正时间 L¹ 有限；那时须使用局部 force norm 的重启定理，或 cutoff 后的 force 同定。不能把这条更广结论冒充当前较窄 API 已覆盖的内容；[Spec:289–296](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/research/A01/Spec.lean:289) 已明确记录该收窄。

端点必须用固定有限积分帽控制所有 t<S；“每个较短区间都有限”不足以保证 S 处的总积分有限。最新 R43 [MaximalEndpoint:15–35](C:/Users/zchi/Documents/ChatGPT/blowup-trees/167-r43-endpoint/formalization/NSFormalization/Section4/R43/MaximalEndpoint.lean:15) 通过真实最大族较短窗口证明 S≤Tmax（含等号）的统一 H² 积分估计；[:38–53](C:/Users/zchi/Documents/ChatGPT/blowup-trees/167-r43-endpoint/formalization/NSFormalization/Section4/R43/MaximalEndpoint.lean:38) 给出非顶性。它们仍含临界 L³ 小量的吸收前件 `hsmall`，没有证明该前件无条件成立，也没有提供 A02 restart 或 A04 无条件继续性。原 Section 4:106–132 的低频普通能量项、force L² 项仍有独立作用，不能删除。

最后，冻结 A04 的 `HigherOrderBound` 要求所有自然阶；可以让主要重启入口只消费 H¹，但不能因此削弱该目标。当前 `Continuation.extendsBeyond` 的实现已经只用它的 m=1，说明“以 H¹ 重启”并非对当前架构的全新发现。

## 8. “保留与调整模块”逐项决定

| 模块建议 | 决定 | 实际处理建议与证据 |
| --- | --- | --- |
| `OrdinaryForcedLocal` 作为高阶辅助 | **接受保留；暂不撤出现行 B1 路线** | :32–61 是真实 finite-order mild + ordinary descent；H¹ 局部基础未完成前仍是现有构造入口。其时间不可冒充 H¹ 球统一时间。 |
| `ContinuationInvariant` 保留窗口机制 | **接受** | :69、156、212、280 保留高阶窗口、角不变性和有界 continuation；不能称其已提供 H¹ 唯一性/重启。 |
| `Propagation` 保留 Grönwall，优先 m=1 | **修改后接受** | [Propagation:73](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/Propagation.lean:73) 是算术定理，本身没有 PDE 阶数；m=1 供应未完成，短期可先走 m=3→H¹。 |
| `GronwallInstance` 主入口简化成 H¹ | **拒绝现在按此直接改写** | :72 的 m≥3、`ClassicalSolutionR` 和 `HasSmoothSobolevPath` 不可移除。先有低阶 PDE 证据或 m=3 降阶消费者，再谈新增入口；保留既有高阶合同供给。 |
| `ForceCap` 复用 MemForceR 的 L¹ 推论 | **接受** | [ForceCap:86、160、169](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/ForceCap.lean:169) 与 A04 Forcing:140/160 给不同紧区间/全局帽；使用时仍要区分范数域。 |
| `AprioriRows` 保留估计、退出构造前件 | **修改后接受** | 对需要经典解的行应如此，当前路线已经遵守；其中纯空间范数比较无需因文件名而禁用。比如 :242、257 与 :301 的前件不同，应按定理前件判断，不整文件废弃。 |
| `SliceWiring` 载体完成后使用 | **接受** | [SliceWiring:134、157、179](C:/Users/zchi/Documents/ChatGPT/blowup-trees/168-a01-persistence/formalization/NSFormalization/Section4/A01/SliceWiring.lean:157) 都是已有 classical solution 与 cylinder/ordinary 路径同定的消费者，不能取代 constructor。 |
| `PressureGauge` 直接复用 | **修改后接受** | 保留 :167/200 收尾；它的前件要求已有压力或梯度的光滑/对称结构，不是压力生成器。 |
| `ProjectedEquation` 已完成、直接复用 | **修改后接受** | :40 可在 classical witness 完成后直接填字段；禁止把方向反用作构造前演化方程。 |
| `Horizon` 改为 H¹ 产生 horizon | **拒绝原地替换；接受未来 API 采用低阶预算** | :106、123、137 是 `HasAprioriBound` 条件下、给定 S 的高阶辅助接口，有真实独立用途。先补 H¹ 定理及同 T classical witness，再按 Spec 选择 API horizon；不改变现有 helper 的含义。 |

应额外明确保留原表遗漏的 `ForcedMaximalRegularity`、`ForcedSourceUpgrade`、`HeatGradientTrace`、`OrdinarySobolevTower`、`OrdinaryForcedTime` 和 A03 m≥2 datum 乘积。它们分别覆盖真实源、升阶、trace、代表、时间导数和低阶乘积的已有工作。

## 9. “停止路线 1–7”逐项决定

| 停止项 | 决定 | 边界 |
| --- | --- | --- |
| 1. 停止从各 q 的 local time 拼共同时间 | **修改后接受** | 接受禁止只对任意 Tq 取 inf 后断言正性；拒绝停止“固定一个基准阶的时间，在同一解上做连续升阶”这一当前有用路线。它能解决普通光滑载体，但不能单独解决 H¹ 统一时间。 |
| 2. 停止 H¹ 下界依赖 A3 高阶先验界 | **修改后接受** | 低阶预算应独立；API 的下界字段仍与 classical witness 的同区间构造共同完成。Horizon:61–66 已区分此事，不应记录成修复了一个现有已实施的循环。 |
| 3. 构造前不用要求 ClassicalSolutionR 的 AprioriRows | **接受** | 这是必要的非循环条件，且 lane 168 已明确执行。纯空间比较工具仍可按真实前件复用。 |
| 4. 不为每个 m 单独造 ordinary field | **接受** | 固定一个 ordinary L² carrier，构造全阶 realizations，直接复用现有 tower；这也减少代表选择的重复。 |
| 5. 不在局部不动点阶段同时造 scalar pressure | **接受** | projected velocity 路线足够；仍需现有投影算子和 source 的真实性，不能把“不造压力”误读为“不证明投影”。 |
| 6. 不引入 Serrin、L∞L³、BMO、涡量准则 | **接受** | A01 当前任务不需要新继续准则。Section 4 已有临界估计属于其原定任务，不能因这一条停止 R43/A05 必需工作。 |
| 7. 不要求 whole-space p∈Hm | **接受** | 保持冻结稿的光滑 scalar 代表、L² 梯度和 gauge；不是放弃压力恢复或低频控制。 |

## 10. 四个工作包的审核

| 工作包 | 决定 | 应包含的可检验交付 |
| --- | --- | --- |
| H1-local | **修改后接受** | 明确低阶完成空间与分布无散；局部外力数据类；L¹H¹→热流 X¹ 估计；X¹ 双线性小时间估计；真实 forced mild 存在、H¹ 连续迹、完整唯一性与黏性/时间预算。只证明一次高阶 local theorem 不算完成。 |
| Persistence | **修改后接受** | 是第二项主要 PDE 工作，包含 H¹ 起步到可用高阶范围、真实 source、同 T 连续高阶迹、相容性和初始值。单个自然数归纳定理可作为最终外观，不能据此把内部证明量称作很小。 |
| Smooth carrier | **修改后接受** | 保留已有 tower；把“空间代表”与“时间 PDE bootstrap/联合光滑适配”分开说明。若输入已是每阶时间 C∞，纯封装相对清晰；但这个输入尚未供给，不能放在包名里隐藏。 |
| Assembly | **修改后接受；拒绝‘主要直接复用即可完成’的成本判断** | 仍须证明原 a/f 同定、真实投影动力学、普通 G 的实值/光滑/无旋性、压力梯度与 momentum、t=0 恢复、同一 horizon 的全部字段。最后才能得到 LocalTheoryAPI；A02 restart 与 A04/R43 continuation 是有独立所有权的后续任务，不能因四包合并而宣称已经解决。 |

四个包可以作为叙述分类，但不是已经证明的最小工作量分解。原建议开头“只有第一项是核心分析”与末尾“第一、第二项是主要 PDE 分析”也不一致；应采用后者并将真实的时间 bootstrap、压力桥明确计入。

## 11. 建议的依赖顺序与暂不实施事项

### 推荐执行顺序

1. **先修研究描述，不先改合同。** 将 §2 的 H¹ 数据类、X¹ 类、黏性缩放和时间约定写成清楚的内部目标；明确低阶 budget 不是现有 `horizonOf`，也不是尚未完成的 `LocalTheoryAPI.horizon`。
2. **完成当前可审查的连续升阶缺口。** 用 lane 168 的真实高 source 和 heat trace，完成正则化 source 对齐、有限 word 统一 Cauchy、连续高阶极限、初值/下降/方程同定。全过程不使用 classical energy 的 classical 前件。这个有限目标有直接供应支持，较之立即大重构更可验证。
3. **补真正 H¹ 基础与低阶 persistence 桥。** 分别证明 §2.4 的线性/非线性估计与唯一性，并证明 H¹→可用高阶范围；只有接口匹配和源项时间类都核实后，才接入第 2 步的高阶段。若采用高阶近似/延展路线，也要证明其由固定低阶解控制、时间不缩短。
4. **在最终低阶 horizon 上得到一个兼容全阶塔。** 区别“固定 q 时间上已经成功”与“对 H¹ 球统一时间已经成功”；复用现有 ordinary tower，不为每个 m 重新选 ordinary field。
5. **从真实 mild 生成每阶时间动力学并统一 bootstrap。** 补 `Ico` 上单侧 t=0 的所有时间导数，再通过现有代表和最少的联合光滑桥得到普通速度。
6. **恢复径向压力并装配原数据的 classical solution。** 先证明实际 Leray 补场的 ordinary 光滑无旋性与 L²，再径向积分；处理符号、实值、初值端点和 momentum。最后复用 gauge/projected 字段定理。
7. **装配低阶预算的 API horizon。** 此时才能合法地同时给 `solution`、`regularity` 和 `horizon_lower_bound`，且下界依赖全正时间 L¹H¹ 的有限 K；无须改动冻结规格。
8. **继续性另行收口。** A02 以该 API 给真实统一重启和 overlap 拼接；A04 优先评估已有 m=3 Grönwall→H¹ 降阶方案，补最大族/hpath/端点运输。R43 最新 G5 可提供其有条件端点 H² 积分，保留尚未证明的吸收前件和其他 owner 任务。

此顺序中的第 2 步可作为当前最小下一项；第 3 步是完成最终 H¹ 架构不可绕过的分析。完成第 2 步不能提前标记整个 A01 完成，完成 H¹ local 也不能提前标记 API horizon 完成。

### 暂不应落实

- 不立即重写 `Horizon.lean`、削弱 A04 `HigherOrderBound` 或更改冻结合同。
- 不删除现有 source/trace、有限阶 descent、窗口不变性、全阶 Grönwall、压力 gauge 等已证模块。
- 不把 `GronwallInstance` 的 m≥3 改成 m=1，除非已经提供新的 PDE 能量证明；优先核实可复用的 m=3 降阶消费者。
- 不新增第二套通用 Sobolev tower；只有核实旧接口不足的具体联合时间/目标 datum 桥才值得增加。
- 不用 `ProjectedEquation`、`PressureGauge` 或 `AprioriRows` 的 classical 前件反向填补 constructor。
- 不以“所有资料已保存”引用 Fujita–Kato 正文；该 HTML 实际缺正文。本轮核心结论已有 Tao 与当前源码支持，无需重复下载资料。

**最终判断：可以采用 H¹ 主导的长期组织方式，但应修改建议的精确规格和成本预期，保留 lane 168 的真实分析成果，并把低阶起步、连续迹、方程兼容和压力反向桥列为明确未完成的证明。**
