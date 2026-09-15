# 165 最终绑定、测试与注册独立复核

## Verdict：ACCEPT；整批交付仍以剩余门禁完成为条件

当前 `Bindings/EnergyAbsorptionV4.lean`、`Tests/EnergyAbsorptionV4.lean` 和 `verification/contracts.json` 的新增 V4 注册可以接受。未发现绑定偷换、常数不一致、父接口丢失或测试遗漏。

已读取实际 `tmp/build_165_Tests_EnergyAbsorptionV4.log`，确认绑定与测试模块成功构建，三个指定公理检查均明确报告 standard logical axioms only。尚未审阅 full lake test / negative / mutations 的完成结果，不能将本报告当成这些门禁已经通过。

## 六字段来源与常数共享

| 字段 | 实际绑定来源 | 处理 |
|---|---|---|
| enstrophyIdentity | C01/EnstrophyIdentity.lean 的同名 theorem | uniqueness_toA02 传解；gradientSq 桥重写目标中的被微分函数 |
| enstrophyDifferentialBound | C01/EnstrophyBounds.lean 的同名 theorem | CRH1=2；gradientSq 桥重写输入 HasDerivAt 的函数，然后传同一个 E′ |
| enstrophyIntegralBound | C01/EnstrophyBounds.lean 的同名 theorem | CRH1=2；目标 gradientSq 的末端/初值项按桥转换；IntervalIntegrable 保留 |
| sobolevTwoFourier | C01/SobolevTwo.lean 的同名 theorem | 直接赋值；CH2=16；真正 angular sobolevENorm，非图范数替换 |
| h2TimeIntegral | C01/H2TimeIntegral.lean 的同名 theorem | Cassembly=32，三项共用；仅 gradientSq a 经已有桥转换；S≤T 未强化 |
| h2TimeIntegralZeroDatum | C01/H2TimeIntegral.lean 的同名 theorem | 同一个 Cassembly=32；零初值实参保持原样 |

三个正性由 norm_num 给出；常数为结构数据，不随 ν、数据、解或时段变化。继承 C₁ 完全不重赋值：V1 绑定设为 gradientL6.Csix，V2/V3/V4 原样携带，与实现中的 A05.gradientL6Const 接口一致；实际构建也验证该实参衔接。

不使用任何研究稿作为 Lean import。V4 contract 只 import 冻结 V3；V4 binding import contract、旧 V3 binding 和生产 C01.H2TimeIntegral；Tests 只 import contract、binding 和 TestSupport.Axioms。注释/registry 引用研究稿作为来源记录不是依赖导入。

## 父接口与 gradient 桥

绑定用 `{ energyAbsorptionPartialV3 with ... }` 构造。`energyAbsorptionPartialV3_of_v4` 的证明精确是 rfl，等式右侧为已存在的冻结 V3 witness；测试明确消费该投影并审计其公理。因此不是复制一组“类似 V3”字段，也没有从 V4 中删除 ordinary energy 部分。

`Bindings/EnergyAbsorptionPartialV2.lean` 的已有桥方向为：

`Contracts.V2...gradientSq z = ∫ x, ∑ i, ‖fderiv ℝ z x (coordinateVector i)‖²`。

它先用 `PiLp.norm_sq_eq_of_L2` 得到 pointwise Frobenius norm-square identity，再用 integral_congr_ae；没有用 operator norm 不等式降弱目标。V4 用 `simp only [energyAbsorptionPartialV2_gradientSq_eq]` 将 contract 侧向实现的 raw sum 方向重写，方向正确。对 derivative 输入 hd 也重写被微分函数，未改 E′。

`Bindings/Uniqueness.lean:63–79` 的 uniqueness_toA02 逐字段保留同一 velocity，其 velocity equality 为 rfl。V4 未创建新的解或时间窗。无需新 mirrored definitions 或新增桥：其他 vocabulary 已由冻结版承接且本次 elaboration 成功。

## 六 shape 与 terminal consumer

Tests 中六个 example 分别完整消费全部新增字段：

- identity 保留实际 HasDerivAt、非线性/ν/forcing 的全部符号；
- differential 保留 ν/4 小量、E′ 和 ν⁻¹；
- integral 保留 Ico 0 T、IntervalIntegrable、末端梯度和初始梯度；
- Fourier 保留 MemHInfty 与 genuine sobolevENorm 的 real-exponent square；
- general H² 保留全部三个项、同一 Cassembly、0<S≤T；
- zero-datum H² 保留精确零初值和相同 Cassembly。

这些是从 checked witness 到独立显式类型的消费测试，不是只 #check 一下声明名字。六字段实际由编译后的同一 record 提供。

`energyAbsorptionV4_terminalFinite` 在调用 h2TimeIntegral 时明确取 S=T，使用 w.horizon_pos 与 le_rfl，得出 Ioo 0 T 上真实 H² 下积分 < ⊤。没有读取 velocity T，也没有附加 T 内严格子区间假设。这是所要求终端用法的实际消费者。

关于下积分可测性/真实 datum 积分语义，沿用 `REVIEW_SPEC_165.md` 已核验的 Data.sobolev + D01 唯一性 + A04 exact norm/continuity 链；此 terminal consumer 本身测试的是 canonical finite lintegral，不应被单独宣传成证明任意 datum path 的实积分转换引理。

## 注册不改旧项

只读 `git diff -- verification/contracts.json` 与 numstat：**11 行新增、0 行删除**，唯一变化是在现有 V3 之后追加 `C01.energy_absorption_v4` 条目。V1/V2/V3 的条目内容未改，enabled 都仍为 true。

PowerShell ConvertFrom-Json 成功读取 registry；C01 四个版本分别指向各自 contract/binding/test 和 checked declaration。新条目 version=4、parent_task=C01、enabled=true，规范路径、模块名和声明名与源码一致。scope 准确披露新增六字段、2/16/32、父 V3 保留、S=T、ν 次幂，以及 critical estimates/bootstrap/Gronwall/continuation 的下游范围；没有宣称后者已完成。

旧 scope 中当时的 “not proved on this branch” 属冻结历史表述，本次未为更新历史而修改它们；新 V4 scope 明确当前新增内容，处理符合版本化约定。

## 实际日志证据与限制

已读取日志末尾：

- Built Bindings.EnergyAbsorptionV4 (10s)。
- Built Tests.EnergyAbsorptionV4 (15s)。
- checkedEnergyAbsorptionV4：checked; standard logical axioms only。
- energyAbsorptionPartialV3_of_v4：checked; standard logical axioms only。
- energyAbsorptionV4_terminalFinite：checked; standard logical axioms only。
- Build completed successfully (10399 jobs)。

日志含既有依赖 replay 的 warning；不能称整个闭包零 warning，但本目标构建成功。没有从纯文本日志推断未记录的 shell exit code；成功状态以日志的明确 completion 及三个 checked 输出为证据。

本次仅源审查、JSON 解析、只读 diff 和已有日志阅读，未重跑 Lean，未改 binding/contract/tests/registry/workqueue/cards/R43。剩余 full test、negative、mutation 结果由后续补齐；若其失败涉及本次更改，应重新评估最终交付状态。
