# 166 ForcedMaximalRegularity 独立源审查

## Verdict：ACCEPT（source-level）

接受 `formalization/NSFormalization/Section4/A01/ForcedMaximalRegularity.lean` 的当前源级数学组装。它对已存在的真实非线性 mild witness，在同一 T 上获得高一阶的 Bochner L² 时间实现；没有偷偷假设 ClassicalSolutionR，没有用另一条解替代原解，没有在最大正则性步骤缩短 horizon。

尚未收到或检查本轮实际编译和 `#print axioms` 输出，本结论不代表 elaboration/公理审计已经通过。只写本报告，未改代码，未运行 Lean/lake/Git。

## 1. hsol 到线性 Duhamel 是真实定义展开

- 新模块 :14–19 的 private coefficientPath 对抽象 Coefficients C 构造连续路径，:22–26 的 nonlinearSource 仅实例化为 coefficients 1 hq f。展开后二者在原解 u 上逐时计算 `(coefficients 1 hq f).apply (timeInclusion hTS t) (u t)`，连续性由 coefficients 的 joint continuity 与实际 u 连续性复合，不假设未知的高阶路径或导数。
- `Source/ForcedCylinderLocal.lean` 的 coefficients/source_eq 给出的 source 是 `P(f−advection u u)`。其中 forcing 字段看似是 −f，但 `source_eq` 明确展开为正确的正 forcing、负 advection；不能仅从该负号误判方程。
- `vendor/.../QuadraticHeatLocal.lean:23–30` 的 quadraticDuhamel 是 heatOperator u₀ 加积分，integrand 中 source 的两个参数是 `timeInclusion hTS (projIcc 0 T hT (t−τ))` 和 `u (projIcc 0 T hT (t−τ))`。
- `vendor/.../VolterraConvolution.lean:20` 的 extendPath 是沿 projIcc clamp。故将 nonlinearSource 代入 `SobolevMaximalRegularity.lean:45–54` 的线性 source 并展开 extendPath，得到上述完全相同的 integrand；热核、ν、hν、u₀、T、hT 都不变，积分变量改名没有实质变化。
- 新模块 :39–40 直接把 hsol 传入 vendor 定理，源级可确认这里依靠 definitional equality，而非假设另一个线性方程或额外误差为零。是否 Lean 在当前环境顺利展开仍待实际编译确认。

vendor 的结论不是包装好的占位 Prop：`exists_maximal_mild_limit` 从实际 approximation Cauchy sequence 的完备极限构造高阶 TimeLp 元素，`maximal_limit_restriction` 用实际低阶收敛识别原 u。本次审查核对该定理与上述直接依赖层，没有重证整个 vendor 解析链。

## 2. TimeLp、积分与同一个 T

`vendor/.../TimeLp.lean:15,23` 精确定义：

- timeMeasure T = volume.restrict (Icc 0 T)。
- TimeLp T E = Lp E 2 (timeMeasure T)。

因此 W 是实际的 Banach 值 Bochner L² 元素，携带强可测性和平方积分有限性，不是给有限积分自取定义的别名。新模块 :41–42 通过 `Lp.memLp W` 及 `memLp_two_iff_integrable_sq_norm` 得到实平方范数 Integrable，排除了仅依赖 totalized 实积分数值的空洞结论。

新模块 :30–42 的所有 T 都是输入 T；vendor 最大正则性定理也固定该 T。:61–90 先取得 OrdinaryForcedLocal.exists_local 的 T,u,U，再用同一 hT、hTS、u 调用该桥，只额外构造 W。没有重新选择较短 T 或新的 u。

必须保留的范围限制：这是**每个固定 q 的原局部 witness 上 same-T**，不是所有 q 共用一个 T 的无限阶塔。exists_local_of_memForce 的量词在 q 之后选 T，不能据此宣称已证明共同 lifespan 上的 H∞ classical solution。

## 3. 高阶兼容性严格是 a.e.

新模块 :36–38/:80–82 是
`restrictOperator (W t) = extendPath u t` 在 timeMeasure T 下几乎处处成立。

- `SobolevRestriction.lean:19–32` 的 restrictOperator 是真实导数字图的降阶 bounded linear map；value_restrictOperator 为 rfl，降阶不改变零阶底层 value。
- `higher_value_ae` :45–56 对上述等式施加 value，再组合逐时 ordinaryLift(U)=value(u)。由 restriction 的 value 定义及 extendPath clamp，得到 value(W) 与 ordinaryLift(extendPath U) **几乎处处**相等。此步没有宣称 W 本身连续。
- ordinaryLift/value 这里是空间 L² 载体中的等式，不能额外宣传为所有空间点上的原始代表等式。
- timeMeasure 用 Icc 不是端点保证：Lebesgue 测度下 {0} 和 {T} 零测。W 的 Lp 代表可在端点改变而不影响任何结论。**不能推出 W(0) 对应初值，不能推出 W(T)=u(T)，不能把 a.e. 兼容性写成端点兼容性。**

另一方面 u 和 U 是闭时间区间上的连续路径，exists_local_of_memForce :71–72 分别保留它们在 0 的确切初值；这是从原局部存在定理拿来的点值等式，与 W 的 a.e. 性质分别陈述，处理正确。

## 4. 真实 force 与初始数据

`C01/JetPaths.lean:86–90` 的 forcePath 由 forceSliceField 构造，field 等于 `fun x => f(t,x)` 是 rfl；:99–110 的每阶 jetLp 连续性从 MemForceR 的 datum path 与 jetOfDatum 连续性取得。它独立于任何 velocity 或 ClassicalSolutionR，也不要求 S 在某个解的 lifespan 以内。整个 [0,S] 的真实力片都保留，包括 t=0。

`Euler/SmoothFieldSobolevTime.lean:39–41` 的 sobolevPath 是这些真实 SmoothL2Field 的 ordinarySobolev realization；没有引入可任意挑选、与 f 无关的 source。

`Source/OrdinaryForcedLocal.lean` 的存在定理接收原 a:SmoothL2Field Space 和物理 divergence a=0，构造 u、U 并分别保留 initial equality。新模块保留这些输入，未新添初始高阶小量、ClassicalSolutionR、PDE 的事先经典可微性、已知 maximal regularity 或待求路径的可积性前件。

注意这里初始数据的接口仍是 **SmoothL2Field + divergence**，不是直接 `a∈Data.initialClassR`；这是被要求复用的原局部接口，没有扩大其输入假设。若要对整个稿件 X_R 直接应用，需要已存在的 datum→jets 载体桥，本模块本身未宣称已完成这层 A01 总合同。

## 5. axioms_maxreg166 源审查

`research/A01/axioms_maxreg166.lean` 实例化 q=6：u 在 H7，W 在 H8。它从实际 MemForceR 与原初始数据推出 witness，保留真实 force slices、ordinary U(0)=a.toLp、逐时 lift/value equality，以及 W→u 的 a.e. 降阶和 W 的平方积分可积。源级是主定理的正常投影，没有把 hsol 另列为 caller 的未满足前件。

文件对 nonlinearSource、forced_mild_maximal_regularity、exists_local_of_memForce、actual_force_order_eight、higher_value_ae 发出 `#print axioms`。这些命令不是声明新公理；也不能把命令存在本身当成公理审计通过。本次没有执行它们。

## 6. 最小性、heartbeat 和必要清理

模块只有一个 private 抽象 coefficientPath、它的 actual source 实例化、一条 vendor 应用、一个 ordinary value a.e. 桥和一条原存在 witness 组装。未发现本批必须做的 simplifier 清理或重构。

:58 的 `set_option maxHeartbeats 800000 in` 只局部作用于 exists_local_of_memForce 的 elaboration/证明搜索资源，不改变 Lean 定理前件、结论、时间区间或内核逻辑。这里存在长的依赖见证组装、连续 Sobolev path 与多层实例推导，局部提高资源与该 elaboration 形态相容；本次没有运行默认限额比较，不能实证声称800000为必要最小值。应依据实际编译记录描述“默认限额不足”与否，不能将它描述成数学条件。

## 验证待补

当前只有源级 ACCEPT。后续应附当前文件的 Lean 编译退出码、axioms_maxreg166 实际输出及是否仅标准公理。若输出只审计该脚本列出的五项，可据此报告其闭包；不要声称本次重新验证了整个 vendor 库或完整 A01 classical local existence。


## r4 最终 source 分层复核补记（编译待确认）

已逐行读取更新后的92行模块。private coefficientPath :14–19 的连续性证明直接复合抽象 C.continuous 与 `(timeInclusion hTS, u)`；nonlinearSource :22–26 只传入真实 coefficients。这样在证明连续性时不必展开 concrete projected quadratic coefficient 的内部结构，是局部 elaboration 分层；它不增加对实际解的新前件，也不增加 public API。nonlinearSource 没有额外 heartbeat 设置；仅 exists_local_of_memForce 仍由 :58 的局部800000包围。

defeq 审计仍成立：现在需要多展开一层 private coefficientPath，但实际函数仍严格是 `C.apply (timeInclusion hTS t) (u t)`，与 quadraticDuhamel 中 clamped source 一致。其余四个公开陈述、same T、真实 force/初值和 a.e. 兼容性没有变化。源级 ACCEPT 维持。

父任务传来的执行状态是：r1 默认 budget 不足；r3 即使给 nonlinearSource 800000 仍失败；r4 已交 Luna 编译中。本补记只记录该状态，不宣称r4已编译成功，也不将r3失败未经诊断地归因于单一原因。此前关于“未实测800000必要最小值”的限制继续有效；最终执行及公理证据等待实际日志。

## 最终验证补记：ACCEPT

已实际读取以下日志，r4 的编译待定状态现在解除，最终接受本模块及本次验证范围：

- `tmp/build_166_ForcedMaximalRegularity_r4.log`：明确记录 `Built NSFormalization.Section4.A01.ForcedMaximalRegularity (18s)` 和 `Build completed successfully (10200 jobs)`。此前 defeq 展开及实例推导的 elaboration 不确定性已由该实际构建消除。日志含上游 replay warnings，不宣称整个依赖闭包零 warning。
- `tmp/probe_166_axioms_maxreg.log`：完整读取五项输出，nonlinearSource、forced_mild_maximal_regularity、exists_local_of_memForce、actual_force_order_eight、higher_value_ae 均恰为 `[propext, Classical.choice, Quot.sound]`；没有额外公理。q=6 的真实 MemForceR、ordinary 初值、H8→H7 a.e. 兼容性实例已实际 elaboration。
- `tmp/lake_test_166_maxreg.log`：实际检查已注册 Tests 的 checked-record 输出，26 个 checked records 均报告 standard logical axioms only；日志末尾运行到 10524/10524。Luna 回报该 full lake test 的 native exit code 为0；文本日志本身不另附该退出码，故区分此执行回报与所读文本。
- `tmp/mutations_166_maxreg.log`：implementation_refactor accepted；admitted_proof、extra_axiom、weakened_hypothesis 均 rejected as required；末尾明确 `Mutation suite passed. This is an infrastructure check, not a PDE proof.` Luna 回报 native exit code 0。

最终 ACCEPT 不扩大数学结论：高阶 W 的识别仍仅时间 a.e.，不是0/T点值保证；same-T 仍为每个固定q的原局部 witness，不是共同无限阶 lifespan。本次只是读取别人已执行的日志、更新 review，没有重跑 Lean 或修改实现。
