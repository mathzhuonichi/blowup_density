# T14 独立草案 B 对照

只读指定的论文、计划、任务卡及注册接口/Section 4 模板；未读取其他草案或禁止目录的内容。本文件不作 A/B 实际比较，供之后 reconciliation 使用。

## 论文条款 → Lean 字段

所有继承字段均指 `PacketImportAPI.toPacketAPI`，沿用 `Contracts.V1.PacketAPI` 的类型，不复制定义。

| 论文位置 | Lean 字段/陈述 |
|---|---|
| 01-introduction.tex:16，每个 ν>0 存在一个包 | `packetImportStatement`：`∀ ν, 0 < ν → Nonempty (PacketImportAPI ν)`；`viscosity_pos` |
| 01:16–19，U,P,F,K 及光滑性 | `velocity`, `pressure`, `force`, `carrier`; `velocity_smooth`, `pressure_smooth`, `force_smooth` |
| 01:17,24–25，紧支撑 | `force_support`, `carrier_compact`, `velocity_support`, `pressure_support` |
| 01:20–22，NS、无散、零初值 | `navier_stokes`, `divergence_free`, `zero_initial_velocity` |
| 01:27–28，有限能量及末端速度无界 | `square_integrable`, `energy_isLUB`, `speed_unbounded` |
| 02-preliminaries.tex:130，M 是准确上确界 | `energyBound : ℝ`, `energy_isLUB` |
| 02:131，D 是准确耗散范数 | `dissipationBound : ℝ`, `dissipation_integrable`, `dissipation_eq` |
| 02:141，N(t) 定义 | `accumulatedForce` |
| 02:147–148，不等式左半 | `energy.energy_le_work`，系数为 `2 * ν` 和 `2` |
| 02:148，右端等于 N(t)² | `energy.work_eq_square` |
| 02:133,152，初始静默 | `quietTime`, `quiet_pos`, `quiet_lt_one`, `force_quiet`, `velocity_quiet`, `pressure_quiet` |
| 02:133,152，负时间光滑零延拓 | `velocity_extension_smooth`, `pressure_extension_smooth` |
| 03-torus.tex:108–111，F 的零延拓约定 | `force_smooth`, `force_zero_nonpos`, `force_support` |
| 03:123,141，延拓后方程和无散性 | `extension_navier_stokes`, `extension_divergence_free` |

## 选择、量词和范围

- 目标标签实际分别在第 1、2 节；第 3 节只是使用它们。T14 是全空间源包接口，不是一个已经周期化的解。物理场继续使用注册的 `Space = EuclideanSpace ℝ (Fin 3)`，时空参数排列为 `(t,x)`。
- 数据结构继承 I01，避免另造七个彼此无关的见证。`energy` 约束的正是继承包；M、D、τ 都允许依赖 ν 和所选包。`packetEnergyStatement` 更进一步明确能量补充可作用于任意已有 `PacketAPI ν`，包括 `Bindings.packet ν hν`，而非仅能选择一个新的包。
- M、D 是实数，因而有限；M 用 `IsLUB` 而非任意上界，D 用非负平方根的准确等式。非负性可推导，不加冗余字段。耗散可积字段防止总化积分把无穷耗散读成零。光滑紧支撑保证每个梯度切片和 F 切片可积。
- `accumulatedForce` 是论文公式的本地直译，已标记 “needs registration / to be aligned with T10”。唯一新增定义无需引入周期 Sobolev 理论；注册时为实现端同式提供 `rfl` 桥。其余定义直接 import 注册合同，无本地副本。
- 时间取 `[0,1)`，积分取 `(0,t)`；Lebesgue 零测端点使这与纸面 `∫₀ᵗ` 一致。t=1 不要求 U 定义良好。负时间延拓光滑域为 `(-∞,1)×ℝ³`，不跨奇异时刻。
- 保留注册接口惯例：PDE 显式在 `(0,1)`，延拓 PDE 则包含 t=0；闭初始静默区间 `[0,τ]` 且 `0<τ<1` 是论文证明中可选的见证。
- `thm:packet` 后的 “Consequently” 全局非存在推论（01:30 起）不是 T14 导入包的消费接口；与 I01 一致未扩入全局唯一性/非存在陈述。论文证明中的微分能量恒等式和 `‖U(t)‖₂≤N(t)` 是证明中间引理，不作为额外 API 字段。

## Section 4 对应物及周期侧边界

对应 U01 的粘性包来源和已注册 I01.packet；`verification/Bindings/Packet.lean` 的 `packet ν hν` 已经供给完整 `PacketAPI ν`。`Section4/I01/Energy.lean` 的 `exists_l2_isLUB`、`Quiet.lean`、`Extension.lean` 分别供给 M、静默、零延拓。注册 I01 **没有** `eq:packetenergy` 的完整数值不等式链；本草案补充它，不声称存在实现。

所有 `PacketAPI` 字段对 T14 的**全空间源包**均可逐字复用，包括 M、D、τ 和延拓字段。`lem:packetenergy` 本身没有新增环面专属条款：它写的是 ℝ³。相对于 I01 的新增要求仅是显示的能量链。

对周期化后的物理场，需要区别“复用源包”与“直接把字段的对象替换成周期场”：

- 光滑性、方程、无散、零初值、静默和末端速度无界，可在单拷贝放置后通过局部相同性转移；这需要引理，并非 Lean 上直接投影原字段。
- 一个非零周期场在 ℝ³ 上不紧支撑。因此 `carrier_compact`/空间支撑、`force_support` 的全空间紧支撑措辞、全空间 L² 积分及 M/D 定义，不能原样断言在周期提升上。应在基本立方体积分，并用单拷贝积分恒等式及缩放因子转移。
- 紧支撑本身不足以保证在单位环面周期化后仍解非线性 PDE：若拷贝重叠，对流项出现交叉项。03:101–120 先取 K_* 包含 K 与力的空间投影，再取小 ε 使 `x₀+εK_*⊂B`，才保证单拷贝。这是 T15 范围。
- 周期压力的均值零规范（02:28；03:123）需要减空间常数，也属于 T15；不能将源包紧支撑压力直接称为均值零压力。
- T10 的系数层应为加权 `lp (Fin 3 → ℤ) 2`，权 `(1+4π²|k|²)^(s/2)`。本节点的源包能量不使用周期 H^s，故不私建代理、占位 Prop、Schwartz 或连续 Fourier 周期范数。周期物理场与系数层的桥留给 T10/T15。

## Needs a lemma

1. 从 `PacketAPI` 的平滑紧支撑和 PDE 推出闭子区间上的积分能量恒等式；保留 ν 和零初值。
2. 正则化平方根给出 `‖U(t)‖₂≤N(t)`；代回恒等式得到 `energy_le_work`。
3. F 的 L² 切片范数在有限时间段连续可积；微积分基本定理给出 `2∫‖F‖₂N=N²`。
4. 本地 N 与实现的定义桥；开区间集合积分与区间积分的等价，包含 t=0。
5. 既有 I01 已解决 M 的 LUB、有限耗散、静默、延拓；T14 绑定只需在同一个 `Bindings.packet` 上补齐第 1–3 项，不能假定注册接口已经含有能量链。
6. 后继 T15：空间/时间缩放、局部有限平移求和与导数交换、单拷贝非线性方程转移、基本立方体 L²/梯度积分恒等式、压力减均值。周期 H^s 比较属于 T13/T15，不加入 T14。
