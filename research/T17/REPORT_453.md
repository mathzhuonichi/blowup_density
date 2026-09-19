# Lane 453 — T17 U12 阻塞报告

## 1. 证了哪个定理

证明 `GeometryObstruction.statedG4_false : ¬ statedG4`：用户指定的 G4
修订陈述仍为假。取 cube centre、chart 半径 `1/8`、`r = 1/4`、
零 packet、非零常向量参考场、`ν = T = δ = 1`，满足全部 G4 假设，
但不满足结论要求的 `CorrectionAPI.ball_in_chart`。

## 2. Lean 里现在有什么

新增 `Section3/T17/AssemblyObstruction.lean`：合法 placement、chart 闭包
包含于 cube 内部、球包含失败、完整 G4 反例及参考场非零证明。
新增 probe、`axioms_u12.lean`、`ATTEMPTS_U12.md`；更新拆分文档 U12 状态。
未添加 assembly、合同、绑定、测试或注册条目，因为目标陈述为假。

## 3. 缺口是什么

必须在 G4 假设块增加
`Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius`。
这是保持 45 字段不变时必要的几何假设。缩小 `D.ε₀` 无法修复它。
已向用户提出该修订，记录时尚未收到答复。没有擅自修改 binding ruling。
U12 未完成；合同数量未增加，work-items 未标记完成。

## 4. 跑了什么命令、什么结果

所有 lake 命令均 source `scripts/lean-env.sh`，从 `verification/` 运行，
`LEAN_NUM_THREADS=6`。

- `lake build NSFormalization.Section3.T17.Correction`：exit 0。
- `lake build NSFormalization.Section3.T17.AssemblyObstruction`：exit 0。
- `lake env lean ../research/T17/axioms_u12.lean`：exit 0；输出如下。
- 根目录 `scripts/gates.sh`：exit 0；末尾输出如下。
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`：
  exit 0；输出摘录如下。46 = base，**不是要求的 base + 1**。
- `git diff --stat verification/contracts.json`：exit 0，空输出。

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

```json
{
  "registered_contracts": 46,
  "base_compatibility_checked": true
}
```

```text
'NSFormalization.Section3.T17.GeometryObstruction.chart_in_cube' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.place' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.ball_not_in_chart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.statedG4_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.reference_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

```text
$ git diff --stat verification/contracts.json
```


# Continuation — completed G4, 2026-09-19

## 1. 证了哪个定理

完成 `NSFormalization.Section3.T17.correctionStatementAmended_holds`，假设块严格采用用户最终裁决：
正粘性、正半径、`r < 1/2`、正余量、周期性、全局光滑、chart cylinder 上散度为零、
raw packet 在 `(0,1)` 的支撑包含于 `K`、以及 `ball place.x₀ r` 包含于 placement chart。
结论同时给出 T16 local potential 与全部 45 字段的 `CorrectionAPI`。
`correctionAPI_of_smooth` 在具体 `correctionData` 上装配，无额外结构假设。

阈值取 `min ε₁ place.ε₀`；T16 的两项小量不等式由区间包含保留，
`place.eps_le_one` 给出 `ε₀ ≤ 1`。`hcube` 由 `closure_mono hball` 和
`place.chartBall_in_cube` 直接推出。没有循环使用待构造的 API。

## 2. Lean 里现在有什么

- 新增 canonical `Section3/T17/Assembly.lean`：45 字段装配、最终 G4 存在定理、完整非空见证。
  非空见证位于 cube centre `(1/2,1/2,1/2)`，chart/requested radius 均为 `1/4`，
  `ν=T=δ=1`，零 packet，参考场 `e₀ ≠ 0`，并显式给出正阈值及 admissible scale `D.ε₀`。
- 新增 `Contracts/V1/Correction3.lean`、`Bindings/Correction3.lean`、`Tests/Correction3.lean`。
  合同外层是 raw-field 拼写和最终 G4；`Packet` namespace 保留 Spec 的 45 字段 record
  与 unamended statement **byte-for-byte**。重复的函数定义都有 `rfl` 桥；record 采用
  双向逐字段转换及往返引理；涉及不同 record 类型的陈述采用双向 fieldwise transport。
  测试独立重述完整假设块，并核查 force profile identity、mixed bound、Sobolev bound 三字段。
- 注册 `T02.correction`，parent `T02`，version 1；scope 写明完整假设块和 G1/G3/G4。
  `work_items.json` 为 T17 添加合同，按现有台账惯例保留 `in-progress` 等待 lead 集成；
  `tasks.py render` 更新生成卡片；U12 数学状态为 DONE。
- 原反例模块移出 canonical tree：删除 `AssemblyObstruction.lean` 及 import-only wrapper，
  内容和 inline `#print axioms` 合并到
  `research/T17/probes/assembly_geometry_obstruction_module.lean`。
  此 probe 单独通过 `lake env lean`，没有 canonical import 指向它。
- 更新 `ATTEMPTS_U12.md`、`axioms_u12.lean`、`T17_SPLIT.md`、G4 addendum、reconciliation
  和 session 记录。此前本报告中的 BLOCKED 结论已被本 Continuation 取代。

## 3. 缺口是什么

最终 G4 范围内没有剩余缺口，deliverables 1–5 均完成。
原始无假设 `correctionStatement` 保留但不声称可证；非正粘性或非周期参考场已与其字段冲突。
中间版 G4 缺少 ball-in-chart 的已接受反例只作为 research probe 保留。
没有改动已有 API 字段、已有稳定合同或已有证明模块，也没有加入 admission 或新公理。

## 4. 跑了什么命令、什么结果

所有 lake 命令均先 source `scripts/lean-env.sh`，从 `verification/` 运行，
`LEAN_NUM_THREADS=6`。以下命令全部 exit 0：

```text
lake build NSFormalization.Section3.T17.Assembly
lake build Bindings.Correction3
lake build Tests.Correction3
lake env lean ../research/T17/probes/assembly_geometry_obstruction_module.lean
lake env lean ../research/T17/axioms_u12.lean
python3 experiments/tasks.py render
BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh
python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
git diff --check
```

记录的是修正 namespace 歧义等 elaboration 问题后的最终通过结果；初次尝试见 ATTEMPTS。
新测试输出：

```text
ℹ [10051/10051] Built Tests.Correction3 (3.0s)
info: Tests/Correction3.lean:20:0: Contract BlowupDensity.Tests.checkedCorrection3: checked; standard logical axioms only
info: Tests/Correction3.lean:69:0: Contract BlowupDensity.Tests.checkedCorrection3_nonvacuous: checked; standard logical axioms only
Build completed successfully (10051 jobs).
```

门禁输出摘录（完整本地日志 `tmp/codex/gates-u12.log`）：

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

Base-aware registry 输出摘录（base 46 → current 47）：

```json
{
  "registered_contracts": 47,
  "base_compatibility_checked": true
}
```

Spec fidelity 检查输出：

```text
Spec packet CorrectionAPI and unamended statement: byte-for-byte equal.
canonical 45 fields
raw contract 45 fields
packet contract 45 fields
```

`axioms_u12.lean` 输出：

```text
'NSFormalization.Section3.T17.correctionAPI_of_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionStatementAmended_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.chart_in_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.place' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.reference_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.nonvacuous_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.ofContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.toContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.ofPacket' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.toPacket' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.correctionStatement_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.correctionStatementAmended_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.Packet.correctionStatement_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.correctionStatementAmended_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.nonvacuous_correction' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCorrection3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCorrection3_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Bindings.Correction3.to_of: checked; standard logical axioms only
Contract BlowupDensity.Bindings.Correction3.of_to: checked; standard logical axioms only
Contract BlowupDensity.Bindings.Correction3.toPacket_ofPacket: checked; standard logical axioms only
Contract BlowupDensity.Bindings.Correction3.ofPacket_toPacket: checked; standard logical axioms only
```

所有打印的构造/定理恰为标准三公理；纯 `rfl` 桥与往返引理可只依赖其子集，
另由 `checkAxioms` 检查。Standalone obstruction probe 的五个声明也均为标准三公理。

```text
$ git diff --stat verification/contracts.json
verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```
