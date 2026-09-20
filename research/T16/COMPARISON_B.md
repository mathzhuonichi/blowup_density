# T16 独立陈述草案 B

仅阅读指定论文、公共计划、已注册 Section 4 合同及本地实现；未读取其他 T16/T10/T13 草案或其 briefs。文件是陈述，不是证明，也没有注册合同。

## 论文条款 → Lean 字段

| 论文 | Lean |
|---|---|
| 03-torus.tex:167–174 光滑 Urysohn 截断 | `theta_smooth`, `theta_compactSupport`, `theta_range`, `plateau_open`, `prescribed_subset_plateau`, `theta_one`；时间对应 `eta_smooth`, `eta_compactSupport`, `eta_range` |
| :181 θ 紧支撑且在 K_* 邻域为 1 | 上述 plateau 字段及 `theta_radius_pos`, `theta_support` |
| :182 η 支撑于 (-2,2)，在 [-1,1] 为 1 | `eta_support`, `eta_one` |
| :177–180 径向向量势 | `potential_smooth`, `potential_formula` |
| :181,196–210 curl A = v | `potential_curl`，仅在原坐标球及参考光滑时间窗内 |
| :184–185 θ_ε、η_ε | 直接使用 `Contracts.V1.Correction.scaledSpatialCutoff/scaledTemporalCutoff` |
| :186 w_ε = -curl(η_ε θ_ε A) | `correction_formula`，在坐标球内 |
| :188,212 足够小 ε | `eps_pos`, `eps_time`, `eps_space` |
| :188,212 全局光滑、无散、周期 | `correction_smooth`, `correction_divergence_free`, `correction_periodic` |
| :188–189 空间及时间支撑 | `correction_support_ball`, `correction_support`，分别记录 |
| :190–193,214–215 eq:bgzero | `correction_cancels`，`Ico (T-ε²) T` 上，开集包含周期包切片的 `tsupport` |

## 选择与量词

`localPotentialStatement` 的次序是：给定 v、U、紧集 K_*、中心、半径、T、δ；假设几何/时间正性、参考周期性、球内光滑无散、包在源时间 (0,1) 的空间支撑包含 K_*；存在一个 `CutoffData`；其中所有结论使用同一个阈值和修正族，并对每个 `0 < ε ≤ ε₀` 成立。不要求 U 的 PDE 或爆破性质，因为本节点只使用支撑；`scaledPacket` 已将非正源时间置零。

`CutoffData : Type` 承载实际函数和实数，`LocalPotentialAPI … D : Prop` 只含具体数学断言。Lean 的 Prop 结构不能提供可投影的任意实数见证，所以不能把 θRadius/ε₀ 直接放进 Prop 记录；存在量词在主陈述里绑定这些数据。本引理没有“universal constant”或范数估计，故没有虚构 C 字段。

物理层沿用已注册的 `Space`、`VelocityField`、curl/cross/divergence，时间在前。局部新增的整数平移、周期性、周期支撑集合、周期包及 b_ε 定义均标记 needs registration / to be aligned with T10。`correctedBackground` 是 v+w 的定义，不把 I02 的同名语义 `corrected_background`（动量方程）错误当作本节点结论。

本节点没有 Sobolev/齐次范数或均值零要求，因此不添加未使用的数据层。后续 T10 的系数代理应采用 `lp (Fin 3 → ℤ) 2`，权 `(1+4π²|k|²)^{s/2}`，齐次权 `|2πk|^s`，均值零即零频系数为零；不可直接搬入 D01 的连续 Fourier/Schwartz 定义。T17 才需要这些范数。

## 歧义与边界

- “坐标球”解释为 `0 < r < 1/2` 的单位环面欧氏球；更大给定开集可先选内部小球。本陈述不宣称所有可能的坐标图都已处理。
- 周期提升的非零场不可能具有 R³ 紧支撑。故没有复制 I02 的 `correction_compactSupport`；空间支撑是整数平移球并集。由周期性、局部公式和支撑条件指定零延拓的周期场。
- 参考只需在 `(0,T+δ) × ball` 光滑。论文的闭时间窗假设更强；时间截断严格落在该开窗内，不需要先构造全局光滑参考延拓。
- K 是调用者指定的 K_*，可同时覆盖包载体和力支撑，与 Section 4 V2 的修复一致。
- `tsupport` 是非零集合的闭包。开邻域结论保留了空间导数也消失这一关键强度。
- `periodicScaledPacket` 的 `tsum` 对任意函数虽为全定义，但只有在主陈述的源时间和紧支撑条件下才按局部有限和使用；需要证明相应支撑桥，不能借不可求和时的 junk 值证明抵消。
- 未加入 T17 的导数/能量/混合范数估计，也未加入 T18 的背景动量方程或交叉输运恒等式。

## Needs a lemma

1. 球内光滑径向积分的参数微分与 curl 恒等式（已有 `Paper1/RadialPotential.lean` 全局版本；需局部化）。
2. 光滑 Urysohn 截断并带 [0,1] 值域；已有 `Paper1/LocalCutoff.lean` 可复用 bump 构造。
3. 从 θ 紧支撑选 θRadius，统一选 ε₀ 使时间与空间严格包含成立。
4. 坐标球内修正的光滑零延拓及其整数平移局部有限和；周期性、curl 的局部性、div curl = 0。
5. 周期提升支撑与球内 `tsupport` 的桥；不能使用 R³ 的全局 compactSupport 结论冒充。
6. 缩放包支撑包含 `x₀ + ε K_*`，非正源时间为空，再将局部有限周期和的支撑提升。
7. plateau 的缩放及周期平移给出覆盖包支撑的开集，时间 cutoff 在 active interval 恒等于 1，从而 eq:bgzero。
8. 新周期词汇与将来 T10 的定义对齐；定义相同用 rfl 桥，表示不同时须实际等价/支撑桥。

## Section 4 对应物

`verification/Contracts/V1/Correction.lean` 的 `BlowupDensity.Contracts.V1.CorrectionAPI` / `correctionStatement`（I02.correction）同时涵盖 lem:potential 和 lem:correction；本草案只取前半的对应字段。`verification/Contracts/V2/Correction.lean` 的 `CorrectionAPI` 添加 `prescribed_subset_plateau`，供调用者指定扩大紧集。`verification/Bindings/Correction.lean` 的 `correction` 是 V1 实现绑定，并有 curl/cross/缩放 cutoff 的 rfl 桥。实现模块 `NSFormalization.Section4.I02.Reference`、`Support` 负责参考局部化及支撑；`Energy`、`Mixed` 对应 T17，非 T16。

Section 4 使用依据见 `04-whole-space.tex:23–29`：向量势是局部的，欧氏球内证明可复用。真正新增的是周期延拓和周期支撑陈述。
