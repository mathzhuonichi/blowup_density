# 278-SPEC-t14-spec 报告

## 1. 证了哪个定理

本 lane 不写证明，完成的是 T14 的最终规格：对一个既有的注册欧氏包
`P : PacketAPI ν`，`PacketEnergyAPI P` 分两个字段逐字保存
`eq:packetenergy` 的不等式与等式；`PacketImportAPI ν` 要求这两个关系约束
的正是它继承的包。另给出论文量词顺序的 `packetImportStatement`，以及供
T15/T17 固定每个正黏性包的 `PacketImportFamily`。

规格严格采用 reconciliation 的 B 包装、`Ioo` 积分域和
`accumulatedForce` 名称，并加入 A 的选定族。`M`、`D`、初始静默区间和
负时间光滑零延拓全部继承 `Contracts.V1.PacketAPI`，没有重复或削弱。

## 2. Lean 里现在有什么

- `Spec.lean` 含 `accumulatedForce`、`PacketEnergyAPI`、
  `PacketImportAPI`、`packetImportStatement` 和 `PacketImportFamily`；每个
  新结构字段都有具体 non-vacuity 说明，docstring 同时标出能量引理的真实
  来源和 `03-torus.tex` 的消费行。
- 文件先 import T10 `Spec.lean` 的同一组基础模块，再 import 注册
  `Packet` 合同。T14 仍是周期化前的欧氏源包，所需 T10 定义的最小集合为
  空，因此没有复制 `PeriodicSobolev`、`IsPeriodicDatum`、
  `periodicSobolevENorm`、齐次范数、`meanT`、`torusLift` 或
  `periodicFourierCoeff`，也没有另造周期代理。此选择及未来注册前的复制
  规则已写入文件头和 `COMPARISON.md`。
- `COMPARISON.md` 合并了论文条款到字段的 A/B 来源和全部 binding ruling，
  并精确列出证明所需的 `Bindings.packet`、
  `Source.PacketEnergy.packet_energy`、
  `Paper1.energy_add_dissipation_le_primitive_sq`、已有 `rfl` 桥及尚需的
  FTC/积分域桥。它也明确指出 T14 对 T10 `COMPARISON.md` 的 17 项待证引理
  依赖集合为空，并列出从 T15 起才需要的第 1、2、3、12 项。
- 两个盲草案的 `DraftA.lean`、`DraftB.lean`、两个 comparison 和
  `REPORT_273.md`/`REPORT_274.md` 已从各自分支逐字加入；逐文件 SHA-256
  与 `git show` 输出完全一致。

## 3. 缺口是什么

- 后续证明/注册 lane 要在同一个 `Bindings.packet ν hν` 上补能量字段。
  已有 `Source.PacketEnergy.packet_energy` 给出折叠后的
  `E+2νD≤N²`；仍需证明 `2∫ bN=N²` 的 FTC 引理、把 interval integral 转为
  `Ioo` set integral，并据此拆出最终两个字段。
- 单拷贝周期化、环面 `L²`/梯度恒等式、压力减均值以及周期 Sobolev 估计
  属于 T15，不应加进 T14。T10 的 quotient/Haar、Parseval 和
  physical/coefficient energy 桥也从那里开始使用。
- owner 仍需决定是否在正式合同中额外公开 Draft B 的全称
  `packetEnergyStatement`、FTC 引理是否公共注册、`T10 → T14` 是否仅为词汇/
  调度依赖，以及最终归入 T01 还是 T02。另一个任务元数据问题是：
  `03-torus.tex:21-60` 实为 `lem:localization`，`lem:packetenergy` 的真实位置
  是 `02-preliminaries.tex:127-153`。

## 4. 跑了什么命令、什么结果

- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T14/Spec.lean`：
  退出码 0，0 errors，0 warnings。
- 同样 elaboration `DraftA.lean` 与 `DraftB.lean`：均退出码 0；B 的预期
  `#check` 信息正常输出。
- `git diff --check`：通过；对最终 spec/comparison 的禁用 token 搜索无
  `sorry`、`admit`、`axiom` 或 `native_decide` 命中。
- `make check`：退出码 0；13 项合同政策测试通过，45 项工作台账一致。
  输出仍报告仓库基线的 `BoundaryCorollary.lean:90` admission 和
  `source_hashes_match: false`，本 lane 未修改这些文件。
- `LEAN_NUM_THREADS=6 make test`：退出码 0；注册测试闭包全部通过，仅有既有
  linter warnings。
- `LEAN_NUM_THREADS=6 make test-mutations`：退出码 0；实现重构被接受，
  admitted proof、额外 axiom、弱化假设三类变异均按预期拒绝，最后报告
  `Mutation suite passed`。
