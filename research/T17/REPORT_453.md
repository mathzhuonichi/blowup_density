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
