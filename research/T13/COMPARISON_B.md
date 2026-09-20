# T13：独立草案 B 的论文对照

仅依据用户指定的论文、注册词汇和既有实现；未读取其他 T13/T10 草案或 briefs。这里的“comparison”是论文与本草案的比较，不是两个独立草案之间的比较。

## 论文子句 → Lean 字段

| 论文位置（03-torus.tex） | Lean 字段 | 量词／含义 |
|---|---|---|
| 35–39，显式 c_s，正且有限 | `constant_pos_finite` | ∀ s，0<s<1；常数是定义的积分，不是任意可选参数 |
| 40–48，R³ Gagliardo 恒等式 | `wholeSpace_identity` | ∀ s∈(0,1)，∀ 光滑紧支实三维向量场 f；I_R 有限且等于 c_s 乘注册齐次范数平方 |
| 58–72，周期 Gagliardo 恒等式 | `torus_identity` | ∀ s∈(0,1)，∀ 立方体平移 a，∀ 光滑周期 f；I_T 有限且等于 c_s 乘去均值后的系数齐次范数平方 |
| 83–88，远处格点求和收敛 | `lattice_summable` | ∀ s>0，∑_{n≠0}|n|^{-3-2s}<∞；此辅助收敛事实不需要 s<1 |
| 80–89，尾和一致界及交换 x,y | `tail_bound` | ∀ s∈(0,1)，∀ d>0，∃ C>0，∀ h；‖h‖≤√3、所有非零格点距离≥d ⇒ 尾和≤C。取 h=x−y 或 y−x |
| 23–28、95–96，eq:localization | `localization` | ∀ s∈(0,1)，∀ 固定 Q、B，∃ C>0，∀ 光滑 f，tsupport f⊆B ⇒ ‖per f‖_{H^s(T³)}≤C(‖f‖₂+‖f‖_{Ḣ^s(R³)}) |
| 29、97–98，s=0 | `endpoint_zero` | 相同 Q、B、支撑条件下，周期化前后物理 L² 范数相等 |
| 29、97–98，s=1 | `endpoint_one` | 相同条件下，物理 L² 梯度范数相等；不把 H¹ 范数与梯度范数混为一谈 |

全部字段都是具体命题。没有任意 `Prop` 占位字段、证明、公理或 API 实例。有限性作为恒等式结论的一部分显式保留，不要求调用者先证明额外的 Sobolev 成员资格。

## 表示选择与精确规范

- **球、立方体及周期化。** `Q a` 是任意平移的闭单位轴向立方体。`AdmissibleBall a c r` 精确要求 r>0、开球闭包包含于 Q 的内部。没有人为的 r<1/4 等附加条件。`f` 直接表示论文的零延拓 z_R，要求全空间光滑且 `tsupport f ⊆ ball c r`。`periodize f x = ∑' n, f(x−n)` 是实际格点和；不接受无约束的“周期代表”。光滑紧支于 B 的原始 z 与这种零延拓表示等价，需桥接引理。
- **均匀性。** 常数出现在 f 之前，不依赖实际支撑的直径或缩放参数。固定 B 中任意进一步收缩的支撑都使用同一个常数。a 记录论文中隐含固定的 Q；换坐标后可固定 a=0，故这不是对场添加额外限制。尾界 C 的量词只允许依赖 s,d，不能依赖 h 或场。
- **积分。** I_R 使用外层 h、内层 x 的非负 Lebesgue 双积分。I_T 使用 Q×Q 上的核积分。使用闭立方体仅改变零测边界，便于直接表达论文的格点尾和比较。Fourier 系数仍通过标准 (0,1]³ 代表的 `torusLift` 与 Haar 积分取得；周期性保证它与任意 Q 的系数一致。
- **系数数据。** `PeriodicDatum = PiLp 2 (Fin 3 → lp Z³ 2)`，外层也是 Euclidean 范数，绝非三个分量的最大值。H^s 权为 `(1+4π²|k|²)^(s/2)`，Ḣ^s 权为 `|2πk|^s`，显式排除 k=0。物理到数据的关系约束所有分量、所有系数。范数对所有实现数据取 infimum；无数据时为 ∞。此处只需要光滑函数，不声称已经定义完整的周期分布空间。
- **均值。** 论文 67 行明确写 `z−ẑ(0)`；草案保留 `removeMean f`，未添加输入均值零条件。`torusHomogeneousENorm` 在一般场上是忽略常数的半范数，仅在去均值场上作为齐次范数使用。`removeMean` 用实际向量 cubeIntegral，实场的零 Fourier 系数即此积分的复数嵌入。
- **R³ 注册层。** 直接使用 `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`，它对满足注册 `IsHomogeneousSliceDatum` 的 `RealVectorSobolev s` 数据取范数下确界。没有拿时间量 `forceHomogeneousENorm` 冒充空间量，也没有引入独立的未约束 Fourier 范数。
- **常数。** `c_s = ∫ |exp(i h₁)−1|² |h|^(−3−2s) dh`，指数没有 2π；R³ 是 unitary angular Fourier convention，T³ 的频率仍为 2πk。两条恒等式引用同一定义，不能分别选择常数。索引 `h 0` 对应论文 h₁。
- **扩展实数。** 常数、积分、核、范数均用 ℝ≥0∞，避免实数 `tsum` 或 `.toReal` 在发散时返回零。c_s 的有限性和正性是显式字段。实幂在零点的总化使单个奇点项取零；核仅在非格点处解释为论文的奇异核。可数格点和双积分中的相关对角线为零测集，需证明零测修改不改变积分。
- **向量／标量。** 原文的上下文是实向量场（01-introduction.tex:103 约定分量平方和）；本草案主接口用注册 `SpatialField : R³→R³`。梯度采用列范数平方之和，即 Hilbert–Schmidt 范数。实标量版本由单分量嵌入得到；没有声称任意复数值／任意维 Hilbert 空间的额外泛化。无需无散或零均值前提。

## 歧义及范围裁定

1. 任务概述的“agree up to constants”可能被理解为双向等价；论文显示式实际只有**非齐次周期范数的单向上界**。草案严格采用显示式，未加反向估计或齐次范数相等。
2. `lem:localization` 的声明本体是上界与两端点等式；用户同时要求证明中的 Gagliardo、c_s 和尾和子句，因此它们也列为 API 字段。中间的 H^s 平方界、I_T≤I_R+4C‖f‖₂² 是证明步骤，列入下方引理清单，不增加独立 API 承诺。
3. “supported in B”取拓扑支撑包含于开球。论文没有给固定数值半径；草案未加入。球闭包与立方体边界的距离严格为正是上述几何条件的结论。
4. 本草案未查看 T10 的独立定义。周期数据名仅为本地候选，后续应与 T10 统一；不能以本草案未经审查的定义替代已注册接口。

## Needs registration

所有新周期／几何／积分定义都在 Lean docstring 中标注。`torusLift`、`periodicFourierCoeff`、`periodicFrequencyWeight` 是指定已有模块的逐字定义体（展开／重命名类型别名）；正式注册时须分别给出 `rfl` 绑定桥。其他定义是本草案新增候选，不能称为已有注册词汇的逐字副本。`UnitPeriods`、`spatialPartial`、`cubeIntegral`、`toSpace` 复用 vendor 词汇；若最终合同 import 白名单不容许该模块，也需逐字注册与桥接。冻结的 V1 文件没有修改。

## Needs a lemma（非占位字段）

1. 光滑支撑于 B ⇒ 紧支；原始球内场的光滑零延拓与 `SupportedInBall` 等价。
2. 紧支格点和局部有限 ⇒ `periodize` 光滑、`UnitPeriods`、在 Q 上等于 f；支撑不碰边界使所有阶导数也单拷贝匹配。
3. `toSpace` 保 Lebesgue 测度；`Q 0` 与 vendor cube 的积分相同；`integral_torusLift` 和 Parseval 的 ENNReal、向量与平移版本。
4. D01 的紧支齐次数据存在、唯一、范数等于 angular Fourier 平方积分，与注册 `dotHomogeneousENorm` 绑定。已有 `HomogeneousWitness` 的 `isHomogeneousSliceDatum_compact`、`enorm_of_isHomogeneousSliceDatum` 等头部可复用。
5. c_s 的可测性、正性和有限性；旋转、伸缩、unitary Plancherel、Tonelli 给出 I_R 恒等式；向量分量求和。
6. 周期 weighted-ℓ² 数据存在、唯一、范数等于加权系数平方和；已有 `PeriodicSobolevHilbert.periodicWeightedFourierLp` 支持 s≤1 的标量非齐次部分，需补向量与齐次版本。
7. 零系数与 cube 平均值桥；减均值不改变非零系数；Parseval 和 Tonelli 给出 I_T 的同一 c_s 规范。
8. 奇点的零测修改、周期核可测性、非零格点 p 级数收敛；‖n‖>2√3 时 ‖h+n‖≥‖n‖/2；有限近格点部分由 d 控制。
9. d=dist(closure B, frontier Q)>0，x∈B,y∈Q 时 ‖x−y+n‖≥d (n≠0)，以及交换 x,y 的版本；将几何应用于 `tail_bound`。
10. n=0 部分≤I_R，其余≤4C_{s,d}‖f‖₂²；由 `(1+r²)^s≤1+r^(2s)` 得周期 H^s 平方界，再开方得所需 C_{s,B}。不要求 c_s 或 C 的数值闭式。
11. 单拷贝积分给出两个端点等式，并与系数 H⁰／去均值 Ḣ¹ 范数建立消费者所需的桥。
