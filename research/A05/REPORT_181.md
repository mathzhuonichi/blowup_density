# Lane 181-A05-v2-contract report

## 1. 证了哪个定理

把 lane 165 已证的 Lemma B.1 阶半速度嵌入的 `MemHInfty`
特例化注册为第 29 个合同
`A05.gradient_l6_v2`：

```lean
∀ v : SpatialField, MemHInfty v →
  eLpNorm v 3 volume ≤
    ENNReal.ofReal (C (1 / 2)) * dotHomogeneousENorm (1 / 2) v
```

这是 `research/A05/Spec.lean:366-368` 的原字段，对应 Lemma B.1 在
`paper/sections/appendix-b-embeddings.tex:29` 的陈述，及 Proposition 4.3/4.4 在
`04-whole-space.tex:93,171` 的使用。`GradientL6V2API (C : ℝ → ℝ)`
结构性继承冻结的 `GradientL6API`，只新增这一个数学字段。绑定选择
常数函数 `fun _ => A05.criticalL3Const`，其中
`criticalL3Const = 3 * scalarCriticalConst (1/2)`，且正性已由
`gradientL6V2Constant_pos` 记录。

## 2. Lean 里现在有什么

- `verification/Contracts/V2/GradientL6.lean`：自包含 V2 API，只导入
  `Contracts.*`；`Ḣ^{1/2}` 直接使用已注册的
  `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`，没有第二份重述。
- `verification/Bindings/GradientL6V2.lean`：用
  `{ gradientL6 with velocityCriticalL3 := … }` 绑定
  `NSFormalization.Section4.A05.velocityCriticalL3`，并显式记录：
  `Data.MemHInfty = A02.MemHInfty` by `rfl`；
  `A05.dotHomogeneousENorm = D01.dotHomogeneousENorm` by `rfl`；再与现有
  D01 contract bridge 复合到已注册定义。`gradientL6_of_v2 := rfl`
  保证 V1 投影没有漂移。
- `verification/Tests/GradientL6V2.lean`：`checkedGradientL6V2`、
  `TestSupport.checkAxioms` 和对 Spec 字段的 conformance example。
- `verification/contracts.json`、`collaboration/work_items.json` 及重生成的任务卡
  现在登记 `A05.gradient_l6_v2`。JSON 保持 UTF-8 字符（等价于
  `ensure_ascii=False`）和两空格缩进。
- 长期记录在 `ATTEMPTS_V2_CONTRACT.md`、`axioms_v2_contract.lean` 及
  `COMPARISON.md` 的 lane 181 注册注记。

## 3. 缺口是什么

本合同只注册已证的阶半速度 `L³` 嵌入。仍未注册：包含
`a = 1` 的 `embeddingPair`、作为合同字段的全阶 `C_pos`、
`criticalRepresentative`、导数和 Bessel 临界 `L³` 子句、
`homogeneousLeSobolev`、`Ḣ^{3/2}` 梯度比较，以及 R43/R44 的 PDE
结论。V1 的 `Csix` 与新的 `criticalL3Const` 是不同定义，没有偷换或
无证明地共用常数。

## 4. 跑了什么命令、结果

`scripts/gates.sh` 从 worktree 根目录运行，exit 0：

```text
== make check
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
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

其中 `extra_axiom` 通过 record update 把
`checkedGradientL6V2.velocityCriticalL3` 替换为额外公理；
`weakened_hypothesis` 直接尝试把该已检查字段的 `MemHInfty` 前提删去。
两个 case 都明确练习 `checkedGradientL6V2`，且均被拒绝。

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`，exit 0：

```text
  "registered_contracts": 29,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A05/axioms_v2_contract.lean`，exit 0：

```text
'NSFormalization.Section4.A05.velocityCriticalL3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2_memHInfty_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2_A05_dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2_dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2Constant_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6_of_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedGradientL6V2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`git diff --stat verification/contracts.json`：

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` 也为 exit 0，无输出。
