# NEXT_SESSION.md — 当前状态与下一步

## 2026-09-15 2110Z 状态（lead 快照；codex 工作流）

- **main 已并入集成分支**（lane 184，merge commit `c0f4439`，153 个 Section4 模块门禁绿，28 合同，vs `origin/main` 兼容）。owner 的模块占原路径，我们的同名模块改名：`C01/EnstrophyIdentityRaw.lean`、`A01/ConstructorDivergenceSlice.lean`（`ForceBridge` 已改 import）。我们的 177/183 取消（被 owner 的 C01 V4 / H2TimeIntegral + R43/MaximalEndpoint 取代）。
- **在跑**（tmux `bd`）：审稿 178（B1 R3）；fix 180（B2 装配：三个命名输入 `hsob`/`hc3`/`hpg`）；fix 176（SIMP rebase 到新基线 + 备注）；181（A05 V2 合同，第 29 个）；182（R43 S1b 三线性估计）；186（**A3-U 公共视界**，astra low）；合并链 PR #185（175 R43 S1）。
- **A01 主线的真正卡点**（178 与 180 的审稿一致）：一个 U 在每个柱阶实现（跨阶唯一性）= 178 的 `hall` 假设 → lane 186；力路径时间光滑 `hfs`（167 的 forcePath → `sobolevPath` 的桥）→ 待开 lane；压力梯度正则性 `hpg`（180 fix 会给出精确陈述）→ 待开 lane；B1 R4 联合光滑 `hc3`。
- 处理顺序：DONE 文件到 → 读 `tmp/codex/<lane>.last.md` → 起审稿（`scripts/codex_review.sh`）→ ACCEPT 则 PR + `tmp/mkchain.sh` 合并链；REJECT 则写 `tmp/codex/briefs/fix_<lane>.md` 起 fix 运行（`codex_lane.sh … fix`）。记录：`tmp/plan_row.py set/add`、`logs/AGENT_RUNS.csv`。未 push 的记录 commit 让合并链吸收，别在链跑时 push。
- **2026-09-15 2200Z 补充**：main 已并入；175/178/181 已合并（#185/#186/#187，29 合同）；176（#188）、186（#189）合并链串行排队中。**180 的接口有设计缺陷**（夹住载体 + 视界 S+1 使 `hc3` 对非定常解不可满足），PR #190 转草稿，fix2 改视界 `T:=S`；188 声称无条件证出 `MildUniqueness`（审稿中）；187（hfs 桥）、189（压力梯度正则性 `hpg`）、182（三线性估计，审稿中）在跑。合并链现在用 `tmp/queue_chain.sh <上一条链窗口> <merge脚本> tmp/chain_lane<NNN>.log` 串行排队并写日志给 Monitor。
- **2026-09-15 2245Z 压力腿重设计（重要）**：189 审稿指出 `pressureGradientOfVelocity := residual − ∂ₜu` 用的是环境双侧 `fderiv`，在 `t=0` 对只在 `[0,S)` 光滑的场是垃圾值，所以任何"压力梯度在 `Ico 0 S` 上光滑/L²"的输入在 `t=0` 都不可满足（`ClassicalSolutionR.momentum` 只在 `Ioo`，但 `pressure_gradient`/`pressure_smooth` 在 `Ico`）。方案：压力梯度改定义为残差 `νΔu+f−(u·∇)u` 的 Leray 余项数据路径（169/178 给出其 C^j_t 正则性）经 190 的联合光滑代表元得到的场 `G_new`；在 `Ioo` 上由 169 的投影动量恒等式得 `G_new = residual − ∂ₜu`（供 168 的 `momentum_of_projected`），在 `Ico` 上直接有光滑与 L²。189 的 fix 等 190 落地后写；180 之后需 fix4 改用 `G_new`。
- **2026-09-15 2320Z A01 管线现状**：`hb`（193：条件于唯一命名输入 `MildGronwall`——有限阶 mild 能量不等式，下一条 lane 194）→ 192（`hU/hdiv/hsob` 合并导出，复审中）→ 190（`velocity/hslice/hc3` 联合光滑代表元，审稿中）+ 189（压力梯度场 `G`，fix 待 190 合入后启动）→ 180（构造器 fix4：以 `velocity/hslice/hc3` 与 `G/hG_int/hG` 为参数，运行中）。合上后经典解构造器只剩 `MildGronwall` 一个分析输入。R43 侧：175+182 已合入，191（U4/U8 shifted 数据）在跑，之后剩 Parseval 配对（可外包）。
- **2026-09-15 2330Z**：193（A3-M2 先验界族，条件于 `MildGronwall`）、192（接线）、191（U4/U8）、190（联合光滑代表元）均已合入（#197/#196/#195/#194；164 模块、29 合同）。在跑：196 `MildGronwall`（astra）、194/195（189 重设计两半，astra）、fix5 180（供给方量词形状：消费者环直接用 190/192 落地定理，189 义务定义为作用于选定解的 `PressureSupply`）。180 前四轮审稿抓到的都是"命名输入对真实供给不可满足"这一类问题（夹住载体、Lp 强制逐点值、t=0 双侧 fderiv、未限定量词），教训已进 LESSONS。
- **2026-09-15 2323Z A3 链**：`FiniteMildEnergy`（标量平方能量包络的微分不等式，下一条 lane 198，astra）→ 196 `mildGronwall`（条件版已证，审稿中）→ 193 `hb_of_base`（已合入 #197）→ 192 → 190/194+195+197（压力腿三块：余项路径、内点恒等式、投影桥 `hprojected`）→ 189 装配 → 180（fix5：供给方量词形状 + `PressureSupply`）。196 指出 `MildGronwall` 应限定无散数据（`ha`），等审稿建议后在 198 里一并 re-cut。
- **2026-09-15 2351Z**：194（#199 余项路径）、195（#200 内点恒等式，条件于 `hprojected`+`hresidualAgreement`）、196（#198 mild Grönwall 归约，`FiniteMildEnergy` 为唯一输入；两个能量谓词已加 `ha`）均合入，167 模块。在跑：198（能量前提，astra）、fix 197（推导柱面 Helmholtz 分解并接 194→195，astra）、180 第五轮审稿（`PressureSupply`）。之后：189 装配（194+195+197 → `PressureSupply`）、199（`Z` 界 + 包络转换 → `FiniteMildEnergy`）、最终 A01 无条件构造器接线。
- **2026-09-16 0037Z 压力腿闭合（条件于 hb）**：197（#201 投影桥）合入后，189 的装配 `pressureSupply_of_pieces` 逐字证出 180 fix6 的 `PressureSupply`（无额外假设，含 `t=0` 的对称 Jacobian），管线探针 `192 → 190 → 189 → 180` 只剩 `hb` 一个分析前提。待办：180 第六轮审稿（PR #190 转正）→ 189 审稿后 rebase 到 180 之上、改为 import 其 `PressureSupply` 定义并删本地拷贝 → 合入；198 审稿（astra）→ 199（`ForcingFamilyBound` + `EnvelopeConversion` ⇒ `FiniteMildEnergy`，需保留耗散的能量恒等式）。届时经典解构造器只条件于 `FiniteMildEnergy`。
- **2026-09-16 0046Z**：180（#190 经典解构造器，六轮审稿）、198（#202 能量前提）合入，170 模块。在跑：189 fix3（import 180 的 `PressureSupply`、A01 构造器管线探针；合入后构造器只条件于 `hb`）、199（`ForcingFamilyBound` + `EnvelopeConversion` ⇒ `FiniteMildEnergy`，astra）。199 若闭合则 `hb` 无条件，A01 经典解构造器在集成分支上无条件成立——届时开一条接线 lane 把 `LocalTheoryAPI`/A01 合同注册为 V2。
- **2026-09-16 0100Z A01 里程碑**：189（#203）合入，171 模块。集成分支上 `research/A01/probes/a01_constructor_pipeline.lean` 的 `local_constructor_pipeline` 仅由 `hb`（全阶先验界族）+ `hf`/`ha`/正性得到 `ClassicalSolutionR ν (velocity(0,·)) f S`；`hb` 由 193/196/198 归约到 `FiniteMildEnergy`（199）。199 闭合后：开 lane 200 把 A01 局部理论注册为合同（初值用 `a` 本身——`velocity(0,·)` 与 `a.field` a.e. 相等且都光滑，需一个逐点桥），并接上 `LocalTheoryAPI.horizon := S₆(ν,a,f)`。
- **2026-09-16 0130Z A3-M2 剩余两块**：199（#204 带号恒等式 + ODE 包络）合入。200（forcing 界）把 `ForcingFamilyBound` 归约到唯一空间估计 `CylinderCommutatorBound`（柱面 word 级 Kato–Ponce 换位子估计，无 PDE/时间）；201（根比较）把 `CylinderRootComparison` 归约到 `CylinderSignedRootLimit`（带号微分不等式沿 198 的最大逼近族取积分极限）+ `mildNormConstant q ≤ E`。两者审稿中（astra）；审稿后各作为条件模块落地，再开 202（换位子估计）、203（带号极限）。这两条闭合 ⇒ `FiniteMildEnergy` ⇒ `hb` ⇒ A01 经典解构造器无条件。
- **2026-09-16 0140Z**：200（#206 forcing 界，条件于 `CylinderCommutatorBound`）、201（#205 根比较，条件于 `CylinderSignedRootLimit`）合入，174 模块。A3-M2 精确只剩两条分析事实，均在 astra 上证：202 `CylinderCommutatorBound`（柱面 word 换位子 Kato–Ponce 估计，纯空间）、203 `CylinderSignedRootLimit`（带号能量不等式沿最大逼近族的积分极限，需保留耗散的带号通道）。两条闭合 ⇒ `FiniteMildEnergy` ⇒ `hb` ⇒ A01 经典解构造器无条件；之后开 lane 204 注册 A01 合同。
- **2026-09-16 0150Z A3-M2 剥到最内层**：202 把 `CylinderCommutatorBound` 归约到逐坐标估计 `CylinderCoordinateTame q hq C`（换位子 = 四个坐标换位子之和、空 word 抵消已无条件证出；剩混合积柱面插值本体，Kato–Ponce 核心）；203 把 `CylinderSignedRootLimit` 归约到 `CylinderSignedEnergyPassage`（未吸收的带号正则化积分估计，ε 根形式；导数 word 平方积分收敛与带号商吸收已证）。两者审稿中（sol）；之后各作为条件模块落地，再开 204（带号通道）、205（逐坐标 tame 估计，可能 re-cut 到角不变子空间）。
- **2026-09-16 0205Z 路由容量波**：sol 与 astra 都返回 "model at capacity"（连 30 秒探针都失败），202/203 的审稿各死了 2–3 次；已用 `tmp/retry_review.sh` 自动交替重试。204（`CylinderSignedEnergyPassage`）、205（`CylinderCoordinateTame`）的简报已写好在 `collaboration/briefs/`，等审稿结果与容量恢复后从 203/202 分支切树启动（astra）。若容量长时间不恢复：下一会话直接按 `tmp/run_wait_launch_*.sh` 的模式起 204/205，审稿可后补。
- **2026-09-16 0212Z**：202（#208）、203（#207）作为条件模块合入，176 模块。A3-M2 现在精确只剩 `CylinderCoordinateTame`（205）与 `CylinderSignedEnergyPassage`（204）两条命名输入；两条 worker 与 202/203 的补审都在 30 分钟休息后自动重试（`tmp/retry_lane.sh`、`tmp/retry_review.sh`，astra/sol 交替）。合并后 A01 依赖链：`CylinderCoordinateTame` ⇒ ForcingFamilyBound（200/202）；`CylinderSignedEnergyPassage` + ForcingFamilyBound ⇒ CylinderSignedRootLimit（203）⇒ CylinderRootComparison（201）⇒ FiniteMildEnergy（199）⇒ MildGronwall（196）⇒ hb（193）⇒ 192 → 190/189 → 180 经典解构造器。
- **2026-09-16 0255Z Section 3 规划**：`collaboration/SECTION3_PLAN.md` 落地（两份只读调研合成）。要点：本地 146 个 `Paper1/Periodic*` 模块都是 R³+周期谓词表示，真 T³ 只有 `TorusCube.lean` 一座桥；OpenAI 包与 HeliCorgi（= 用户给的 ns-mns2-flowmap-bridge）均为 R³；决定保留物理场的周期表示、分析全放系数侧 `ℓ²(Z³)`（照抄 D01 数据形式架构）；HeliCorgi 抽象 mild/延拓层可在 T³ 载体实例化；`lem:localization`（T13）是最高杠杆的新节点；两条独立脊柱（构造 vs 障碍）可并行。第 4 节做完后再启动。
- **2026-09-16 0300Z 包络侧闭合**：204（astra）无条件证出 `CylinderSignedEnergyPassage`（带号极限通道，保留完整耗散），组合后 `CylinderSignedRootLimit`/`FiniteMildEnergy` 只剩 forcing 侧输入 `ForcingFamilyBound`（⇐ 202 的 `CylinderCommutatorBound` ⇐ 205 的 `CylinderCoordinateTame` ⇐ `SmoothCylinderCoordinateTame`：光滑 H^∞ 场的逐坐标混合积插值）。205 审稿在问：竞争者角不变时能否下降到 R³ 用 A03 tame 积直接证——若能，A01 无条件就只剩接线。
- **2026-09-16 0330Z**：204（#209 带号通道，无条件）合入，177 模块。206（astra）把柱面 word 插值（常数 1）和左向混合积估计证出，但 `SmoothCylinderCoordinateTame` 还差反向估计、Leibniz word 识别、组合求和；它判定角不变下降路线受阻（`ForcingFamilyBound` 无不变性 binder、最大逼近点处不变性不可得）。206 审稿（astra）要给出决定：(A) 继续柱面装配（纯记账）还是 (B) 把 forcing 链 re-cut 到 173 的 `HasAprioriBoundInv` 不变类后下降到 R³ 用 A03。202/203/205 的补审在休息后依次重启（03:35–03:45Z）。
- **2026-09-16 0405Z**：202/203 补审 ACCEPT（产物入记录）。astra 也进入重连/容量波：205、206 审稿被杀并挂休息后重启（sol 优先）。207（tame 装配，路线 A：反向混合积 + Leibniz 识别 + 组合求和 ⇒ `SmoothCylinderCoordinateTame` ⇒ … ⇒ `hb` 无条件 ⇒ A01 无条件构造器探针）已建树，安装后休息 20 分钟自动以 astra/sol 交替启动。若 206 审稿推荐不变类 re-cut（路线 B），用 fix 简报改向。
- **2026-09-16 0440Z A01 局部理论（待审）闭合**：207（astra）走路线 A 证出 `SmoothCylinderCoordinateTame`（显式常数），forcing 界、`FiniteMildEnergy`、`hb` 全部无条件；里程碑探针 `a01_constructor_unconditional`：仅由 `hf`/`ha`/正性得到 `∃ S>0`（基阶局部存在视界）上的 `ClassicalSolutionR`。对抗式审稿在跑。落地顺序：205 → 206 → 207 三条链串行（207 依赖前两者的模块）。之后：把 A01 局部理论注册为合同（`LocalTheoryAPI` 形状：`horizon := S₆(ν,a,f)`、初值 `a` 的逐点桥、压力规范），并让 A02 `exists_maximal`/A04 `restart` 改接它。
- **2026-09-16 0500Z A01 里程碑（无条件）**：207（#212）合入，180 模块，集成分支 `ca5dadb`。`research/A01/probes/a01_constructor_unconditional.lean`：仅由 `hf : MemForceR f`、`ha`（无散光滑 L² 初值）、正性得到 `∃ S>0, ∃ w : ClassicalSolutionR ν (velocity(0,·)) f S`；A3-M2 无任何命名分析输入（`hb_of_base''`）。下一步（自动启动）：208 初值识别 + 总视界函数 + `solution` 字段；209 `ManuscriptLocalRegularity` 四字段；210 `horizon_lower_bound`（H⁷ 一致 + H¹ 子句评估——**spec 问题待 lead/owner 决定**：实现 H¹/H³ 定量局部理论，或 V2 re-cut 到 H⁷）。之后 211 把 `LocalTheoryAPI` 注册为合同（A01 V2），A02 `exists_maximal`/A04 `restart` 改接。
- **2026-09-16 0510Z spec 问题（待用户/owner 决定）**：`LocalTheoryAPI.horizon_lower_bound`（`research/A01/Spec.lean:300-345`）要求视界在 **H¹ 球**（初值 `sobolevENorm 1`、力 `forceSobolevENormL1 1`）上一致，出处是论文 Appendix A 引 Tao 2013 Thm 5.1(ii)/5.4(ii) 的 H¹ 局部理论。树里没有带外力的 H¹ 定量局部理论（vendor Picard 需阶 ≥6，HeliCorgi 是 H³ 无外力）；210 证出了 H⁷ 初值球 + H⁶ 时间上确界力界下的一致视界，并指出 L¹ 时间力范数控制不了 vendor 的 sup 预算、`Classical.choose` 的视界无一致选择（后者可在 211 里用一致存在定理选视界解决）。**lead 建议**：A01 V2 合同把该字段 re-cut 为"固定力、H⁷ 初值球一致"（`∀ ν>0, ∀ f∈F_R, ∀ K≠⊤, ∃ δ>0, ∀ a, sobolevENorm 7 a ≤ K → δ ≤ horizon ν a f`，δ 可依赖 f）——A04 的重启（唯一消费者，REVIEW.md M5）只在同一力下重启且 Grönwall 已界住所有 H^m 范数，故足够；H¹ 版本保留为单独命名的开放字段/后续 lane。若用户/owner 坚持 H¹ 原文，需要一条实现带外力 H¹（或 H³）定量局部理论的大 lane。
- **2026-09-16 0541Z A01 装配完成，只差合同措辞**：208（#213）、209（#214）、210（#215）已合入，211（#216 已合并、门禁在跑）。集成分支上 `Section4/A01/LocalTheoryBundle.lean` 提供 `LocalTheoryAPI` 除 `horizon_lower_bound` 外的全部字段（`localHorizon′` 由一致定理反单调选出；`manuscriptLocalRegularity_localCarrier`；`horizon_lower_bound_H7_fixedForce` 已证；H¹ 原文只作 def）。**212（V2 注册）两份简报已备好**：`collaboration/briefs/212-A01-contract-v2-option1.md`（固定力 H⁷ 收窄，owner 批准后注册为字段）、`…-option2.md`（保留 H¹ 原文，先注册不含该字段的 Partial API）。用户/owner 决定后用对应简报启动。
- **2026-09-16 0554Z spec 问题扩展到 A04**：213 把 A02 的 `exists_maximal` 无条件接上了；但 A04 的 `Restart`（owner 的 `Continuation.lean`）是"δ 只依赖 ν 与 **H¹** 界、对所有初值/外力/重启时刻统一"的 Prop，与 A01 能给的"固定外力、H⁷ 球统一"形状不匹配（平移后的力随 t₀ 变化）。论文自己的重启论证（Appendix A:147-150）是固定外力：`f` 在 `[0,S+1]` 上有界 ⇒ 所有平移力的 sup 范数有共同界 ⇒ 一个 δ 对所有 t₀ 成立。**因此同一个决定同时覆盖 A01 的 `horizon_lower_bound` 与 A04 的 `Restart`：re-cut 为固定外力 + H⁷（选项 1），或实现带外力 H¹ 局部理论（选项 2）**。213 的审稿正在给出 `Restart` 的精确 re-cut 与 `HigherOrderBound`↔179 的桥。214（R43 Parseval）完成待审。
- **2026-09-16 1915Z**：**Prop. 4.4（a=0）无条件 + Theorem 4.1(ii) 两个 q 的非稠密子句都证完**：229（astra，7 分钟）整合 228 的 S1d（单调性适配到 227 的常数）、`rcritical2_endpoint_unconditional`、`not_breakdownDenseR_zero_L2`。227（#231）合入。229 审稿中；231（R44 V1 合同注册）、232（R41 `nonDensityZero` 两个 q 的装配）叠放在 229 上启动。R41 剩稠密分支（R41D ← R42 lifespan 子句），子代理正在调研 R42/R41D 现状。
- **2026-09-16 1845Z**：226（#230）合入——**30 个合同**，R43 Prop. 4.3 注册完成。228（sol，14 分钟）证出 S1d 吸收（自选常数 θ=(4C₀)⁻¹、C₂=3/2、C₃=3），但与 227 在 `R44` 命名空间重名且常数不同，不单独开 PR；新开 229（astra，基于 227）：改造 228 的模块 import 227、按单调性实例化 227 的 `RCritical2Differential`，得 Prop. 4.4 的 a=0 无条件结论 + R41 q=2 非稠密子句。227 审稿中。
- **2026-09-16 1830Z**：226（R43 V1 合同，第 30 个）审稿 ACCEPT → #230 合并链中。227（astra，16 分钟）把 Prop. 4.4 的 a=0 端点装到只差 S1 微分不等式 `RCritical2Differential`（常数固定：θ = min(criticalConst, 1/(100(C_emb+1)³))，C₂=2，C₃=4，radius ν S = θ/20·ν^{3/2}·e^{−3νS}；E′ 可积性只要求在闭预奇异窗口）。228（sol）在证 S1d 吸收；若其常数与 227 不一致，需要一条适配 lane（同时做 Prop. 4.4 无条件化 + R41 q=2 非稠密）。
- **2026-09-16 1800Z**：**Prop. 4.3 全部证完**：225（astra，6 分钟）`universal_of_memForceR` 逐字同 Spec（同一 `criticalConst`）；223（#225）`inhomogeneousAtZero` 已合入。224（#227，R41 q=1 非稠密）已合入。新开 226（sol，基于 225）：注册 R43 V1 合同 `R43.critical_regularity`（第 30 个）。审稿中：220（S1c）、225。接下来 R44：S1d + Prop. 4.4 装配（等 220 合入）；R41 q=2 非稠密等 R44。
- **2026-09-16 1740Z**：**R41 第一块**：224（astra，5 分钟）证出 thm:Rmain (ii) 的 q=1 非稠密子句 `not_breakdownDenseR_zero_L1`（Data 词汇逐字；`forceSobolevENorm_mono_order` 对任意 q 与 s ≤ s′）。223（#225）、222（#226）合并链中。新开 225（astra，基于 223）：R43 `universal` 一般初值子句。220（S1c）续跑仍在跑。
- **2026-09-16 1735Z**：**R43 里程碑**：223（astra，8 分钟）证出 `inhomogeneousAtZero_of_memForceR`——Spec.lean:243-247 逐字（a=0、`forceSobolevENormL1 (1/2) f < criticalConst·ν` ⇒ `maximalLifespanR ν 0 f = ⊤`），无具名输入；`criticalConst = min(1/(8C₀), 1/(4C₁C_emb))`。这是 R41 消费的 R43 子句。审稿中。221（#224）已合入。R43 剩：`universal`（一般初值，含 C01 V4 一般数据 H² 预算）与合同注册；接下来看 R41 拆分表。
- **2026-09-16 1520Z**：容量波约 3.5 小时后恢复：222 续跑（astra）完成 R44 S1b `energy_identity` 无条件；221 续跑（astra）完成 R43 G2/G3/G4 力路径 + `critical_bootstrap_zero_datum`（a=0 时 y ≤ cν）无条件。两者审稿排队（容量重试）。新开 223（astra，基于 221）：R43 端点定理 `inhomogeneousAtZero`（T_max = ∞），走 221 bootstrap → S3 门 → C01 V4 → G5 粘合 → 217 延拓判据。220（R44 S1c）续跑仍在容量重试。
- **2026-09-16 1400Z**：219（#223）合入：**eq:Rcritical1 对任意经典解无具名输入**。218（#222，R44 S1a）合入。09:52Z 一波 model-at-capacity 同时切断 220/221/222 三条工作车道（草稿都已写出未提交）：220 续跑（astra，fix）已启动，221/222 续跑休息 30 分钟后自动启动（`tmp/retry_lane.sh … 1800 fix`，续跑 brief = `tmp/codex/briefs/fix_<lane>.md`）。
- **2026-09-16 1330Z**：**R43 里程碑**：219（astra）闭合 `CriticalDatumInputs`，`rcritical1_of_classical'` 让 eq:Rcritical1 对任意经典解（ν>0，MemForceR 力）**无任何具名输入**（216 乘子是 CLM、齐次数据唯一性、215 式局部载体窗口覆盖、`A04.momentum_datum` 的二阶导数恒等式经 `lowerVectorL` 传到半阶）。219 基线无 215，故把 215 的 7 条支撑声明复刻为 `R43.CarrierWindow`（合入后可选清理）。审稿中。R43 剩：G2/G3 时间积分的齐次力路径（L¹_t Ḣ^{1/2} 可测路径、原函数、FTC）、S2 bootstrap、S6 `inhomogeneousAtZero`。
- **2026-09-16 1230Z**：216（#221，R43 半阶载体）合入，189 模块。218（R44 S1a：`Jmul`、权恒等式、力对偶，负阶载体 `RealVectorSobolev (-1/2)` 已有）完成、审稿中。在跑：219（astra，闭合 `CriticalDatumInputs`，基于 216）、220（sol，R44 S1c J 权三线性，基于 218）。R44 S1b（微分 Y²、消压力）等 219 的整数阶动量恒等式落地后再开，可直接复用。
- **2026-09-16 1100Z**：215（#219）与 217（#220）都已合入（审稿均 ACCEPT 无修改）。**A04 里程碑**：固定力 + H⁷ 形状下，重启窗口、Grönwall→`HigherOrderBound`、`ShiftedLocalExtension` 与三条延拓定理对 `MemForceR` 力全部无具名输入。Section 4 本地模块 188。在跑：216（R43 半阶载体，sol）、218（R44 S1a J 权恒等式，sol）、213 事后审稿（退避中）。等用户定 V2 措辞后启 212（A01 V2）并配套 A04 V2 注册（`Restart` 的固定力形状 = 215 的 `RestartFixedForce`）。
- **2026-09-16 1010Z**：217（astra，约 50 分钟）把 `ShiftedLocalExtension` **无条件**证出（用 A02 的 `velocity_unique_core`/`pressure_gauge_core` 与 `normalizePressure` 在内点 (b+T)/2 拼接归一化压力，不需要时间截断）；`restartBeyond_of_memForceR'`、`extendsBeyond_of_memForceR'`、`lifespanInfiniteOfLocallyFinite_of_memForceR'` 无具名输入。**A04 的延拓/重启对 MemForceR 力已在固定力 + H⁷ 形状下闭合**；剩的只是 owner 的 `Restart`（H¹、跨力）措辞（V2 决定）。217 审稿中；合入顺序 215 → 217。
- **2026-09-16 1000Z**：215（astra）完成：`restartFixedForce_of_memForceR`（固定力、对所有 t₀∈[0,S] 与 H⁷ 数据一致的 δ）与 `higherOrderBound_of_gronwall`（A04 `HigherOrderBound` 定义原样）**无条件**；A04 三条延拓定理的固定力副本已证，`…_of_memForceR` 推论只剩一个具名输入 `ShiftedLocalExtension`（从 b 重启的经典解拼回原问题 ⇒ 寿命 ≥ b+L）——lane 217（astra，基于 215 分支）在证：重叠区速度由唯一性相等、压力用时间截断凸组合。215 审稿中。**215 报告也确认：A04 消费者不需要跨外力一致性，V2 只需把 f、S 放到 δ 之前并把初值界改为 H⁷——支持选项 1。** 216（sol）在做 R43 半阶载体。
- **2026-09-16 0900Z**：214（#217 R43 Parseval）合入，185 模块；213（A02 `exists_maximal` 无条件 + A04 重启前提）lead 复核后 PR #218 合并链中（两次审稿都在 60–70 分钟后被路由 524/容量打掉，事后再审）。215 已开：`RestartFixedForce`（固定力、对所有重启时刻一致）+ 179→`HigherOrderBound` 桥 + A04 延拓定理的固定力副本，**不改 owner 的 `Restart` 定义**——V2 措辞等用户决定。
- 坑：新 worktree 必须先 `LEAN_SEED_DIR=<root> bash scripts/lean-install.sh`（否则 lake 私 clone Mathlib 从源码编译数小时）；`pkill -f` 会杀自己。

## Integration handoff (2026-09-15)

The A01 and C01/R43 dependency chains are consolidated in this tree. PR #161
is the final delivery to `main`; PRs #162–#170 have been merged through their
original parent branches. The dated notes below preserve the original proof
provenance and limitations; their unmerged labels and claims that the sibling
branch is absent are historical.

Use `research/A01/IMPLEMENTATION_PLAN_169.md` for the current A01 plan. C01 V4
and `Section4/R43/MaximalEndpoint.lean` are present. The endpoint result still
requires absorption; the full local constructor and unconditional continuation
remain open. Integration validation and the cloud CI limitation are recorded in
[MERGE_DEPENDENCIES_20260915.md](logs/MERGE_DEPENDENCIES_20260915.md).

- **2026-09-15 文档整理**：`PLAN.md` 重排（§4 节点状态看板、§5 并行工作包、§6 并发与预算；旧 §4/§5 原文在 `logs/PLAN_HISTORY_20260913.md`；进度表现在是 §8，`tmp/plan_row.py` 不受影响）；新增 `collaboration/HANDOFF.md`（11 个可分发工作包 P1–P11，串行骨干 + 并行链，外部协作者 lane 号 200–299）。`collaboration/TASKS.md`/`tasks/*.md` 仍是 `tasks.py render` 生成物，`DESIGN.md` 是工程设计依据，二者不动。
- **2026-09-15 协调（重要）**：owner 已把 PR #15 合入 `main`（`main` = 集成分支到 b7895f1），并开了 **PR #161**（`codex/158-160-formalization-resume` → `main`，作者 mathzhuonichi，基于 `main`，不基于我们的 lane 分支）：重写了 `A01/ConstructorPieces.lean`（4 条定理，把 datum 存在性扩到全阶 `m ≤ q+1`）、`research/A01/CONSTRUCTOR_SPLIT.md`，并完成了 lane 160 的内容（`A04/Continuation.lean`：`restartBeyond` 以 `Restart` 为假设、`lifespanInfiniteOfLocallyFinite` 以 `HigherOrderBound` 为假设；`A04/ForceShift.lean`）。**处理**：我们的 158 分支与 160 工作树不再合入；`research/A01/REVIEW_CONSTRUCTOR_SPLIT.md` + `rev158_*` 探针在 #161 合入 main 后作为跟进 PR 贡献（它们对 #161 的模块仍有价值：N1/N3 已被 #161 吸收，N2/N4/N5 待核）。**流程变化**：现在有两条合入路径（我们 `erenup/integration` → `main`，owner `codex/*` → `main`），每次 owner 合入后集成分支要先 `git merge origin/main` 再开新 lane；HANDOFF 的 P1 已由 owner 团队做完（#161），P7/P8 的一部分（顶三阶、路径连续）也在 #161 里。
- **2026-09-15 2031Z 协调升级**：owner 在 `main` 上用 codex 并行做了与我们**同编号同题**的 lane 158–169（PR #161–#170），并合入了我们的文档 PR #171。`main` 现有：完整 **C01 V4** `C01.energy_absorption_v4`（六字段：enstrophyIdentity、enstrophyDifferentialBound、enstrophyIntegralBound、sobolevTwoFourier、h2TimeIntegral、h2TimeIntegralZeroDatum）、A04 `Continuation.lean`（restartBeyond/extendsBeyond/lifespanInfiniteOfLocallyFinite，以 `Restart`/`HigherOrderBound` 为假设）、C01 `H2TimeIntegral`/`EnstrophyBounds`/`SobolevTwo`、R43 `MaximalEndpoint`（G5）、A01 `ConstructorDatumPath`（≈我们的 161）/`ForcedMaximalRegularity`/`ForcedSourceUpgrade`/`HeatGradientTrace` 与 `IMPLEMENTATION_PLAN_169.md`。**处理（lane 184）**：把 `main` 合进集成分支——同路径冲突取 `main`（`C01/EnstrophyIdentity`、`A01/ConstructorDivergence`），我们的版本改名保留（`EnstrophyIdentityRaw`、`ConstructorDivergenceSlice`，后续 SIMP 去重），`contracts.json` 取并集（28 条），记录两边保留；我们的 177（V4）、183（H² 端点）取消。**今后规则**：每次开 lane 前 `git fetch origin main` 看 owner 侧有无同题；owner 的 codex lane 号请用 HANDOFF 的 200–299 段（已在 HANDOFF 写明），我们的 lane 号继续 1xx。

## 169-A01-plan（2026-09-15，当前执行方案）

- 依据独立 Astra xhigh 审核完成 [H¹ 实施方案](research/A01/IMPLEMENTATION_PLAN_169.md)，并修正旧 split 的 horizon、时间动力学与构造依赖。审核原文归档在 [REVIEW_H1_REFACTOR_169.md](research/A01/REVIEW_H1_REFACTOR_169.md)，保留审查时的证据路径。
- 本 lane 从 PR #169 的 `75bfb4e` 派生，worktree `169-a01-plan`，分支 `codex/169-a01-plan`。仅文档变化；独立 Astra xhigh 复核 ACCEPT，make check 的四个 Python 子命令通过，详见 [验证记录](logs/VALIDATION_169_20260915.md)。已推送 [PR #170](https://github.com/mathzhuonichi/blowup_density/pull/170)，base 为 PR #169 分支；未合并。首个方案 head `9e55927` 的 architecture 检查 `104341112912` 因账单/额度未启动，lean-contracts `104341129148` 跳过。
- **下一全局 lane 170**：先完成 lane 168 实际正则化源对齐 → 有限 word 差值 uniform Cauchy → 连续高阶极限 → 初值/降阶/方程同定。保持同一 witness 与 T，不调用依赖经典解的能量来构造经典解。
- 可并行推进真正 H¹-local 及低阶 persistence 供给。当前 q≥6 升阶不能直接接 H¹；固定基准阶时间上的全阶载体与 H¹ 球统一时间分别验收。
- 后续顺序：低阶预算上同解全阶塔 → 真实 mild 全阶时间 bootstrap（含单侧 t=0）→ 普通压力与经典解 → 同 horizon 完整 API → A02 restart / A04 端点延拓。保留现有 tower、Horizon 辅助接口与冻结高阶合同。
- 代码仍交 Astra low，全部 Lean 编译交 Luna high。平行 PR #168 的 R43 G5 仍有 `hsmall`，不代表无条件延拓或 A05/G7 完成。此前云端 CI 因账单/额度未启动，不记为 Lean 验证通过。

## 168-A01-persistence（2026-09-15 0942Z）

- 已推送 [PR #169](https://github.com/mathzhuonichi/blowup_density/pull/169)，base为PR #167分支。proof head为05b0ca0；architecture检查104331776975因账户账单/额度未启动，lean-contracts跳过；PR未合并。

- 实际高阶sourceTime及同原源a.e.降阶已通过；从166同一local witness构造，保留原T、数据、force和方程。另已证明真实regularized heat终端gradient energy加耗散界及pointbound。
- 两模块、九项标准公理输出、26条现有合同、变异及Python检查全部通过，独立review ACCEPT。见logs/VALIDATION_168_20260915.md；下一步为实际正则化源对齐、有限word差值的uniform Cauchy估计与连续高阶极限，不把time-L2当continuous。
- 平行R43已交付 [PR #168](https://github.com/mathzhuonichi/blowup_density/pull/168)：真实最大族G5端点H2积分界，含S=T_max，仍保留吸收前件。该PR在另一堆叠分支，本tree不含其证明；R43 G7/A05和A04无条件延拓仍开。全局下一lane号169。

- 从 PR #167 / d64704f 派生；同T时间L2升阶之后的连续高阶持续性；源审计并证明关键跨阶桥，禁止循环调用经典解能量。
- 独立worktree和proof缓存，固定依赖；所有Lean编译交Luna high，代码交Astra low。原稿第4节和冻结合同仍为目标。


## 166-A01-maxreg（2026-09-15 0915Z）

- 已推送 [PR #167](https://github.com/mathzhuonichi/blowup_density/pull/167)，base为PR #164分支。proof head为7faf625；architecture检查104323252207因账户账单/额度未启动，lean-contracts跳过；PR未合并。

- 实际 forced mild 方程的同T最大正则性已通过：保留真实外力与原数据，构造高一阶 TimeLp 路径、a.e.降阶和ordinary载体兼容性及平方范数可积性。固定q的T不缩短；不声称T与q无关或高路径连续。
- 模块、五项标准公理输出、26条既有合同、变异和五项Python检查通过；见logs/VALIDATION_166_20260915.md。下一分析缺口仍是低阶寿命上的连续高阶持续性，再构造共同全阶塔与时间光滑性。

- 从 PR #164 / 65b2afb 派生；实际forced mild方程的同horizon TimeLp升阶及真实外力消费者。
- 代码由Astra low编写，所有Lean编译交给Luna high；独立worktree与proof缓存，继续堆叠PR。
- 原稿第4节和冻结合同仍是目标；本lane不注册新合同，也未使用ClassicalSolutionR作为构造前件。


## Lane 163（2026-09-15 0830Z）

- 已推送 [PR #164](https://github.com/mathzhuonichi/blowup_density/pull/164)，base为PR #162分支。云端architecture检查104309961813因账户账单/额度未启动，lean-contracts被跳过；PR未合并。

- 本地模块、8项标准公理输出、26条既有合同、13政策测试、计划/合同/队列/base兼容和变异检查已通过，详见 `logs/VALIDATION_163_20260915.md`。
- `CONSTRUCTOR_SPLIT.md` 已更新c6与有限阶datum进展；旧constructor研究目标缺时间光滑强迫，须保留原版 `MemForceR f` 和实际输入同定。反例路线未Lean形式化。
- 下一真实步骤见 `research/A01/NEXT_CONSTRUCTOR_ROUTE_163.md`：实际forced mild → 同horizon的TimeLp高一阶；共同连续全阶tower与时间bootstrap仍未完成。

- 从 PR #162 / a4e18a2 派生；证明柱面无散约束到 ordinary L2 无散子空间的反向桥，再给实际光滑代表元的逐点散度结论。
- 本 lane 独立 worktree：163-a01；代码由 Astra low 编写，所有 Lean 编译由 Luna high 执行。既有三个 PR 均未合并，按父分支继续堆叠 PR。
- 正式数学目标仍是原版第 4 节与冻结合同；主目录新增 revision 文稿明确不是形式化依赖。

## Lane 161（2026-09-15 0710Z）

- 分支 `codex/161-a01-datum-path`；基线 `0b8e5e4`（PR #161，尚未合并）。已提交 [PR #162](https://github.com/mathzhuonichi/blowup_density/pull/162)，以该 PR 分支为 base；尚未合并。
- 全阶定量下降控制 datum 差，构造所有 m ≤ q+1 的连续 RealVectorSobolev 路径；Luna 模块与顶阶消费者检查 exit 0，七项仅标准三公理；五项仓库 Python 检查、26条现有合同及变异检查全部通过。编写使用 Astra low，所有 Lean 编译使用 Luna high；独立 proof build 缓存，共享固定依赖。
- GitHub CI 的已知阻塞为账户账单/额度，不能据此声称云端验证通过。完整第 4 节形式化尚未完成。

## 167-R43-endpoint（2026-09-15 0935Z）

- 已推送 [PR #168](https://github.com/mathzhuonichi/blowup_density/pull/168)，base为PR #166分支。proof head为e2d05ad；architecture检查104329375348因账户账单/额度未启动，lean-contracts跳过；PR未合并。

- G5实际最大族端点界及A04平方积分有限性已通过，包含S=T_max，原吸收前件不变。模块、四项标准公理、27合同（29checked）、变异和Python检查全部通过；见logs/VALIDATION_167_20260915.md。
- 下一R43关键义务仍为A05临界嵌入与G7临界能量及bootstrap；A04无条件延拓仍依赖A01构造/持续性。全第4节尚未完成。

- 从 PR #166 / b436f72 派生；实际最大解族的吸收H2积分界推至有限最大寿命端点；保留原吸收前件，不假设终点经典解。
- 独立worktree和proof缓存，固定依赖；所有Lean编译交Luna high，代码交Astra low。原稿第4节和冻结合同仍为目标。


## 165-C01-full（2026-09-15 0910Z）

- 已推送 [PR #166](https://github.com/mathzhuonichi/blowup_density/pull/166)，base为PR #165分支。proof head为0fce54c；architecture检查104321156138因账户账单/额度未启动，lean-contracts跳过。PR保持未合并。

- V4完整C01合同、绑定、六字段形状与S=T消费者已通过；27合同、负向hsmall检查、变异测试和五项Python门禁通过。C01工作卡为assembly/in-review，旧合同和测试不变。
- 双盲稿、逐字段协调、独立spec/binding review及全部验证见research/C01与logs/VALIDATION_165_20260915.md。
- 下一步优先R43 G5：以实际IsMaximalSolution的短区间经典解统一估计，推到有限T_max；见research/C01/NEXT_R43_ENDPOINT_165.md。A01连续全阶正则性与A04无条件延拓仍未完成。

- 从 PR #165 / 31621e5 派生；完整C01新版本合同：双独立论文盲稿、陈述比对、绑定和注册验证。
- 代码由Astra low编写，所有Lean编译交给Luna high；独立worktree与proof缓存，继续堆叠PR。
- 原稿第4节和冻结合同仍是目标；C01两份草稿在只读原论文/合同词汇后独立形成，先比对再注册。


## Lane 164（2026-09-15 0835Z）

- 已推送 [PR #165](https://github.com/mathzhuonichi/blowup_density/pull/165)，base为PR #163分支。云端architecture检查104311372421因账户账单/额度未启动，lean-contracts被跳过；PR未合并。

- 已完成真实Sobolev datum H²比较（CH2=16）及一般/零初值时间积分（同一个Cassembly=32），保留S≤T，终点S=T消费者得到有限积分。
- 两模块、6项标准公理输出、26合同、13政策测试、计划/合同/队列/base兼容及变异检查通过，见 `logs/VALIDATION_164_20260915.md`。
- C01下一步是完整合同新版本：按CLAUDE要求由两名互不可见代理从原论文和规范词汇起草、比对，再注册绑定和测试，保持冻结V1/V2/V3不动。本lane仅证明层与原Spec消费者；完整第4节仍未完成。

- 从 PR #163 / 032e5bb 派生；用真实弱导数/范数桥推进 sobolevTwoFourier 与包含 S=T 的 H2 时间积分，保持原Spec前件。
- 本 lane 独立 worktree：164-c01；代码由 Astra low 编写，所有 Lean 编译由 Luna high 执行。既有三个 PR 均未合并，按父分支继续堆叠 PR。
- 正式数学目标仍是原版第 4 节与冻结合同；主目录新增 revision 文稿明确不是形式化依赖。

## Lane 162（2026-09-15 0710Z）

- 分支 `codex/162-c01-enstrophy`；基线 `0b8e5e4`（PR #161，尚未合并）。已提交 [PR #163](https://github.com/mathzhuonichi/blowup_density/pull/163)，以该 PR 分支为 base；尚未合并。
- 装配 E5 梯度能量时导数、E6 压力消失与 E7 分部积分，完成精确 enstrophyIdentity、微分界和积分界（CRH1=2）；两模块及三个原Spec消费者编译通过，八项公理仅标准三条；五项Python检查、26条现有合同及变异检查全部通过。编写使用 Astra low，所有 Lean 编译使用 Luna high；独立 proof build 缓存，共享固定依赖。
- GitHub CI 的已知阻塞为账户账单/额度，不能据此声称云端验证通过。完整第 4 节形式化尚未完成。后续：C01 新版本合同注册、H2/Fourier 比较与 H2 时间积分；A01 连续 datum 路径已由平行 PR #162 验收，下一步 c6 无散下降。

## Codex 本地恢复（2026-09-15；当前状态优先于下面的历史记录）

- 云端 PR #15 已于 2026-09-15 0248Z 合入 `main`；本地预编译基线为 `da640be`，与云端一致。旧文中的「PR #15 待 owner review」已失效。
- 当前恢复分支：`codex/158-160-formalization-resume`，从 `main` 开出；通过新 PR 向 `main` 交付。旧 Linux 工作树和未提交 reviewer 探针不在这台 Windows 主机上。
- 从云端 `erenup/158-A01-b1-constructor-split`（`47cf101`）恢复 lane 158 的五个源文件/研究文件；按暂停记录补全顶阶 datum 与连续 derivative-word 路径，再继续 lane 160 的 R1/C1。
- 本轮用户指定：代码由 `gpt-6-astra` / low subagents 编写，Lean 编译与验证由 `gpt-5.6-luna` / high subagent 执行。主 agent 负责云端对齐、审查、记录与 PR。
- Windows 环境：先 `. .elan/env.ps1`，`lake` 从 `verification/` 运行，复用现有缓存和 `LEAN_NUM_THREADS=1`；不使用旧 Linux 的环境路径。
- 云端最新 `main` CI（run `34922570431`）仍因账户账单/额度未启动，`lean-contracts` 被跳过。不能把该失败记为 Lean 失败或成功；本轮以实际本地验证结果交付。
- 本轮 158 / 160 代码、源码审查和本地验证已完成：3 个新增模块、4 份研究探针、26 条现有合同、13 项合同保护测试及变异测试全部通过。详情见 [`logs/FORMALIZATION_RESUME_20260915.md`](logs/FORMALIZATION_RESUME_20260915.md)。已提交 [PR #161](https://github.com/mathzhuonichi/blowup_density/pull/161)，面向 `main`，待审查，尚未合并。
- 158：datum/弱导数提升到所有 `m ≤ q+1`，导数词普通 L² 路径连续；完整经典解构造子仍欠联合光滑性、共同时间区间、datum 范数连续性及数据/外力同定。
- 160：外力平移界与 R1/C1 装配已证；最终 R1 保留精确 A02 `Restart`，最终 C1 另保留精确 G3 `HigherOrderBound`。两项分析输入未证明，未新增无条件 PDE 合同。
- 后续继续 A01 B1/B2/A3 和原计划 G1 → C01 E5–E7 → A05 U1–U7 → R43 G7；下面 09-14 的恢复顺序保留为历史，其中 158 / 160 已由本轮推进。

更新：2026-09-14 0122Z（erenup 侧）。规矩看 [`CLAUDE.md`](CLAUDE.md)，全貌和顺序看 [`PLAN.md`](PLAN.md)。

## 现状（2026-09-14 0122Z）

- 分支模型：根目录直接检出 `erenup/integration`；lane PR 由 lead 合；**PR #15 integration → main 已交 owner**。`.claude/` hooks/skills；`scripts/gates.sh [modules]`、`scripts/merge_lane.sh`；坑 `logs/LESSONS.md`。
- **CI 无额度（owner 账单）→ 本地替代 CI**：每条合并链跑 `scripts/gates.sh` + 全部 Section4 模块编译 + `check_contracts --base-ref origin/main`；并定期整跑 CI 工作流的三步对 main（`check_contracts` / `build_changed_lean` / `test_contract_mutations --skip-build`，日志 `tmp/ci_equiv_main.log`）。最近一次 09-14 1216Z（含 157 合入后，集成 42dc58e）：全部通过（26 合同、改动模块 10607 jobs 编过、mutations 过）。PLAN.md 进度表带 UTC 列。
- **CI 仍被 owner 账单挡住**；每次合并后本地 `scripts/gates.sh` + 全部 `Section4` 模块显式 build（最近：92 模块、全绿）。合并链脚本用 **`bash tmp/mkchain.sh <lane> <PR> <wave> "<PR 标题>"`** 生成（不要再 sed 上一条脚本：094/103/105/106/108 五个 squash commit 标题因此错成同一句话；PR 标题与 `Merge pull request #N` 提交是对的）。
- integration 上 **24 条注册合同**（+`A04.energy_high_partial` #134，+`A04.energy_high_partial_v2` #141：`Cgron`/G2/G2b）（今日新增：`R42.insertion_lifespan` #95、`B02.homogeneous_partial` #99、`A01.regularity_partial` #111、`R42.insertion_lifespan_v2` #115、`B02.homogeneous_partial_v2` #116、`D01.datum_lemmas_v3` #122 = P2）；已合入 Section4 证明模块 **100+**；2026-09-13/14 共合入 PR #72–#128（约 53 条 lane）。
- 里程碑（追加 09-14 0200Z 后）：**A2b 收口**（134 `forced_global_of_bound_unconditional`：先验界 ⇒ 全区间局部理论输出含角不变性）；**G2/G2b eq:highcontinuation 已证**（135 微分形、138 积分形，均与 spec 逐 token 全同；常数 `Chigh²/(4ν)` 紧）；**C01 eq:RL2 词汇桥**（136，`l2Sq`/`pairing` 对 spec 为 rfl，装配演示已闭合代数）；**A04 首个合同已注册**（133）；**C1b 载体桥在有限阶闭合**（132 D01 侧 + 140 Euler 侧：从 `exists_local` 的 `U` 得每阶 `m ≤ q−2` 的角向 datum，`T=T(q)`；140 已合入；A3-L1·k 的空洞警告解除，只剩定量构造子 145）；**A3 脊柱接近合龙**：A2b 无条件续接（134）、力积分帽（137）、`horizon := S` 打包（139 已合入）、Grönwall 实例化（142 已合入）——每阶 `H^m` 显式界只剩二阶帽 `Kbnd`；142 审稿证明对每个 `T₀<T` 这个帽白送，真正欠的是端点 `T₀=T`（= eq:criterion 本身）；`HasAprioriBound` 还欠三行：反向范数比较（柱面 ≤ R³）、`Ico→Icc` 加宽、mild⇒energy 桥；eq:RL2 算术核心（131）。；**C01 能量恒等式无条件闭合（143 Ep/E3 → 146 E4a → 148 E4b → 150 E4，PR #152）**；**A3-L1·k 算术闭合（145 定量构造子 `16^m` → 147 `Kbnd := 256R²T₀`，PR #147/#149）**，149 加宽 + 反向比较（PR #151）；**eq:RL2 已证（154，PR #156）**：`‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f‖₂` 对任意 `ClassicalSolutionR` 于 `Ico 0 T`；**载体桥词恒等式全阶闭合（151 + 153，PR #153/#155）**；**eq:RL2 已注册为合同（156，PR #157，第 26 条）**
- 里程碑：**P2 = eq:Rpressure 已证并注册**（117 `D01/PressureJets.lean`，120 `D01.datum_lemmas` V3）；**A04 eq:Rhigh 已组装**（121 `hpr` 经 Leray 补算子自伴 + 速度 datum 横向，128 `energyIdentityHigh` 与 spec 字段 127 token 全同）——A04 合同待开，但先做硬规矩 2 的盲写双稿（130，进行中）；**B02 V2、R42 V2 合同已注册**；**A01 起步扎实**：E1/P1/m4 已证并注册；C1b 0 阶桥（119）+ 0 阶 datum 路径连续（124）已证，C1b 真正阻塞 = D01 有限阶 datum 构造子（125：升阶步已证，剩角向搬运 M）；A3 算术核心（122）；A2b 续接（126：从先验界得全区间 mild 解，一行套 vendor；角不变性欠全局 mild 唯一性）；122 审稿改判 OpenAI 层有续接判据（`Euler/BoundedMildContinuation.lean:39`），A2b 不再是 L；123 搬 pairing 文件消除 D01→A04 反向边；SIMP 已过 D01 早期/R42/A01/A04 SL3+SL5 簇（P2 链五模块在跑 129）。
- **并发**：2026-09-14 0205Z 起用户要求降到 **2–3 个 subagent**（API 限额）；优先级：关键链（A04 合同/G2/G3、A01 A2b/C1b/A3、C01 E2）> SIMP/MAINT。
- **在跑（09-15 2027Z，codex worker 机制）**：worker 175（R43 S1 恒等式层，续跑）、178（B1 阶梯 R3）、180（B2 装配）；review 176（SIMP 不变性审计）、177（C01 V4 合同保真）。**已合入的 codex lane（13 条）**：161、162、163、164（第 27 条合同）、165（A05 临界嵌入 `velocityCriticalL3`）、166、167、168、169、170、173（角不变性 β）、174（R41D 定稿）、179（Grönwall 端点：整个 `Ico 0 T` 上不退化的显式界 + A04 restart 输入形状的一致 H¹ 界）。模块 140，合同 27（177 合入后 28）。上游 sol 今晚偶发「model at capacity」：worker 被打断就用 `resume_<lane>.md` 续跑，review 换 astra。
- 小尾巴（MAINT，下次 SIMP 顺手）：`research/C01/Spec.lean` 里 `(:103)` 出现两处（156 审稿 note 3 指的 `04-whole-space.tex:104`「including times where ‖u‖=0」），lead 只改了合同与 registry，Spec 的两处留待 SIMP；`Contracts/V3` 已按 `:117/:132/:104/:118-121` 修正。
- **E4 路线（143 审稿已裁定）**：走 (a) 时间正则单元——五块中三块已有（`(u·∇)u` 喷流连续 vendor `SmoothEulerEvolution.lean:29`；`Δu`/`ν•` 由 `continuous_jetLp_directionalField` + `addField`/`mapField` 拼；力路径镜像 `velocityField_jetLp_continuous`，`MemForceR` 给 `ContDiffOn ℝ ∞ G`；`lerayComplement` 本是 CLM `LerayDatum.lean:255`），真正新的只有动量残差 `f − (u·∇)u + νΔu` 的时间连续 order-m datum 路径（M–L，实质是喷流连续 ⇔ datum 路径连续的双向范数桥，与 145 定量构造子同源）。(b) 经 A02 唯一性搬运更贵：树里尚无构造 `ClassicalSolutionR` 的定理（A01 未落地），且 vendor 自己把 `hB` 当假设（`SmoothEulerEvolution.lean:47`、`OrdinaryEulerDifference.lean:25`）。146 做 (a) 的 S 半；M–L 半等 145 落地后开。
- 已知未入 CI 闭包：`Section4/*` 大多不在注册合同 Tests 闭包；CI 只靠 `build_changed_lean.py`。MAINT 清单（109 之后剩）：**`A04/LaplacianPairing`+`RealPairing` 整体搬到 `Paper3/`**（115 审稿：`D01/LerayLowering` 反向 import A04，两文件不用任何 A04 声明，21 个名字零碰撞）；`PressureGauge.pressureGradient_apply` 与 `D01/MomentumSlice.pressureGradient_apply` 重复（共享 Source 级 `pressureGradient` 演算模块）；`Pressure.pressureGradient_slice_smoothSquareIntegrableJets` 已无人用且更弱（docstring 过时）；111 的 `lerayComplement_orderZeroDatum_add/_sub` 成死代码；`angular_plancherel` + 8 个 B02 helper 整簇上提到新 `Paper3/AngularPlancherel.lean`（低优先级）；108 的 `longitudinal_of_longitudinal_symm` 上提；`OrderZeroDatum`/`HalfOrder` 小副本；B02 数据链副本；074 三条交换引理与 vendor 重复；`contDiff_slice_pressure` 副本**保留，不再翻**（109 已量化）。

## 下一步

1. 回来的车道 → reviewer → 续改 → PR → `tmp/mkchain.sh` 合并链 → 门禁（lead 不手改 Lean）。链串行，一次一条。
2. 待开（按顺序）：**130 comparer**（三方比对 A/B/128 → `BLIND_RHIGH.md`）→ **A04 部分合同** `Contracts/V1/EnergyHighPartial.lean`（`Chigh`/`Chigh_pos`/`energyIdentityHigh`；重述 `HasSmoothSobolevPath`/`sobolevNormAt`/`gradientSobolevNormAt` 各配 rfl 桥，128 审稿已验；绑定经 `uniqueness_toA02`；顺手收 `gradientSobolevENorm_velocity_ne_top` 进 Continuity）；A04 G2 eq:highcontinuation（Young + ζ 正则化，`Regularized.lean` 已有设备）→ eq:criterion；D01 `D-b-transport`（`memLp_coord_smul_datum`，M）+ 对 m 归纳收掉 C1b-m-D；A2b 角不变性（需 OpenAI 圆柱方程的全局 mild 唯一性或逐窗传播）；A3-L1·k 二阶范数比较；B1（速度 jet 连续 `∀ j, Continuous (jetLp j)`）；MAINT：`componentCLM`/`orderZeroDatumCLM` 搬 D01、`isSobolevDatum_zero` 三处副本、PressureJets/PressureDrop 横向论证共享引理、108 四处重复上提；C01 能量/涡量字段（可由 `pressure_drop` 的 m=0/1 实例 + 时间正则性）；I03 U7c；R43/R44（等 A04 G2）；A02 `restart*`（等 A01 H1，`forced_uniform_restart_time` 是线索）。
3. 每次收工更新本文件；agent 运行记 `logs/AGENT_RUNS.csv`；坑记 `logs/LESSONS.md`；Attempts 放 `research/<ID>/ATTEMPTS*.md`。

## 待 owner 决定

- **CI 被 GitHub 账单挡住（2026-09-13 14:54Z 起）**：所有 run 立即失败，annotation 为 "The job was not started because recent account payments have failed or your spending limit needs to be increased"。owner 需在 GitHub Billing & plans 处理。此前最后一次全绿 run：34759326799（13:15–14:43Z，10 条合同 + 全部已合模块）。恢复前合并只靠本地 `scripts/gates.sh` + 显式 build 全部 `Section4` 模块。
- PR #15 `erenup/integration` → `main` 待 owner review（内容已远超首版：22 条合同、100+ 模块，P2 已证并注册，eq:Rhigh 已组装）。
