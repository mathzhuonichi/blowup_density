# Lane 423 — T22 U-REG

## 1. 证了哪个定理

将已闭合的 `orderZero`、`cutoffMultiplier`、`zeroExtensionComparison`
装配为 canonical `boundedDomainNorm : BoundedDomainNormAPI`，注册
`T04.bounded_domain_norm` V1（parent task T04）。保持所有实数阶、先选常数
再量化字段的顺序，以及域商范数的原始分布定义。

## 2. Lean 里现在有什么

新增 `Section3/T22/Assembly.lean`、`Contracts/V1/BoundedDomainNorm.lean`、
`Bindings/BoundedDomainNorm.lean`、`Tests/BoundedDomainNorm.lean`。
API 含注释逐字来自 Spec，七个重述词汇逐一有 `rfl` 桥；两个独立结构体
有双向字段转换、往返等式及 statement 等价。非零 `ContDiffBump` 见证在
`closedBall 0 (1/2) ⊂ ball 0 1` 上实例化全部实数阶的零延拓比较。
新增 attempts、逐声明 audit，更新 U-REG 状态及台账并 render。
原 42 条注册项不变，仅增加一条，JSON 保持 ensure_ascii=False、indent=2。
未修改任何既有 Contracts/V* 或 Tests 文件。

## 3. 缺口是什么

数学及注册无剩余缺口。字面公理输出要求有两项例外：合同结构体和它的
`Nonempty` statement 别名显示无公理依赖；其他 37 个命名声明均恰为
`[propext, Classical.choice, Quot.sound]`。以下保留全部实际输出，不人为
引入依赖。请求保留的 Prop-valued def 及转换 def 有 defProp 风格警告，
Tests 的 warningAsError 编译通过。范围不包含任意域数据上的有界零延拓
算子、边界/no-slip 结论或 T23。全局 mutation suite 是基础设施测试。

## 4. 跑了什么命令、什么结果

所有 Lean 命令先 source `scripts/lean-env.sh`，线程数为 6，lake 仅从
verification workspace 运行。以下全部 exit 0：

- `lake build Tests.BoundedDomainNorm`：9947 jobs，成功。
- `BASE_REF=origin/erenup/integration-section3 scripts/gates.sh`：三个 gate 通过。
- 另行 `make test`：通过，确认脚本的输出过滤没有掩盖失败。
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`。
- `lake env lean ../research/T22/axioms_ureg.lean`。
- `python3 experiments/tasks.py render`、`git diff --check`。

Gates 输出节录：

```text
== make check
  "registered_contracts": 43,
Ran 13 tests in 0.044s
OK
45 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/BoundedDomainNorm.lean:28:0: Contract BlowupDensity.Tests.checkedBoundedDomainNorm: checked; standard logical axioms only
info: Tests/BoundedDomainNorm.lean:33:0: Contract BlowupDensity.Tests.checkedBoundedDomainNormStatement: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
== gates OK
```

Base-aware checker 输出节录（base = 42，当前 = 43）：

```json
{
  "registered_contracts": 43,
  "base_compatibility_checked": true
}
```

`git diff --stat verification/contracts.json`：

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

逐声明 audit 完整输出：

```text
'NSFormalization.Section3.T22.boundedDomainNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.boundedDomainNormStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.boundedDomainNormStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T22.nonvacuityΩ' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityK' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityBump' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityΩ_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityK_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityK_subset_Ω' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.boundedDomainNorm_nonvacuity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.DomainTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.DomainFunctional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.restrictDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.domainSobolevENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.restrictField' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.IsCutoffDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.BoundedDomainNormAPI' does not depend on any axioms
'BlowupDensity.Contracts.V1.BoundedDomainNorm.boundedDomainNormStatement' does not depend on any axioms
'BlowupDensity.Bindings.BoundedDomainNorm.domainTest_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.domainFunctional_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.restrictDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.domainSobolevENorm_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.restrictField_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.zeroExtension_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.isCutoffDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.toCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.ofCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.ofCanonical_toCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.toCanonical_ofCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.boundedDomainNormStatement_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.boundedDomainNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.boundedDomainNormStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Tests.checkedBoundedDomainNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedBoundedDomainNormStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

本 lane 在 `erenup/423-T22-UREG-contract` 本地提交；未 push、merge 或 rebase。
