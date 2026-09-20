# 489-MAINT：消除 T22 `boundedDomainNorm` 的 `defProp` warning

## 改了什么

把 `NSFormalization.Section3.T22.boundedDomainNorm : BoundedDomainNormAPI`
从 `def` 改成 `theorem`，证明项仍逐字是
`⟨orderZero, cutoffMultiplier, zeroExtensionComparison⟩`。这是一个
`Prop`-valued 声明；消费者审计确认它只被当作证明项、字段投影来源或参数传递，
没有消费者用它的可约展开做 `rfl` bridge。因此没有改陈述、证明或语义，也没有用
`set_option linter.defProp false` 隐藏 warning。

`research/T22/axioms_ureg.lean` 重新审计后，
`NSFormalization.Section3.T22.boundedDomainNorm` 及所有相关证明声明仍只依赖
`[propext, Classical.choice, Quot.sound]`。

## 文件

- `formalization/NSFormalization/Section3/T22/Assembly.lean`：唯一源码改动，
  `def boundedDomainNorm` → `theorem boundedDomainNorm`。
- `research/MAINT/REPORT_489.md`：本报告。

`Contracts/V1/*`、`Tests/*`、bindings 和所有 research probes 均未修改。
工作树原有的未跟踪文件
`collaboration/briefs/489-MAINT-t22-defprop-warning.md` 未改、未纳入提交。

## 缺口

数学与实现缺口：无。两个正向 research probes 都以退出码 0、零输出重新 elaboration；
axiom audit 也通过。

有一个既有 reviewer-only **负向** probe
`research/T22/probes/rev423_negative.lean`。它把 multiplier bound 的常数改成
`C / 2`，文件注释明确要求该结论 “must not close”，而且源码故意没有
`fail_if_success` 包装。因此直接执行 `lake env lean` 按设计返回退出码 1 和 type
mismatch；它不可能同时满足“负例应被拒绝”和“直接 elaboration 零输出”。本 lane
保持该 probe 不变，并确认它仍被拒绝。错误核心输出是：

```text
../research/T22/probes/rev423_negative.lean:21:2: error: Type mismatch: After simplification, term
  boundedDomainNorm.cutoffMultiplier
...
but is expected to have type
...
  ‖B‖ₑ ≤ ENNReal.ofReal (C / 2) * ‖A‖ₑ
```

目标模块的 build 会 replay 上游依赖中已有 warnings，但
`NSFormalization/Section3/T22/Assembly.lean` 自身为零 warning。`make test` 仍显示
`verification/Bindings/BoundedDomainNorm.lean` 中三个既有 `defProp` warnings；它们不在
本任务指定的 Section 3 声明范围内，未改。

## 命令和结果

环境均先执行 `. scripts/lean-env.sh`；所有 `lake` 命令均从 `verification/` 运行，
build 使用 `LEAN_NUM_THREADS=6`。

1. 目标模块：

   ```sh
   cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.Assembly
   ```

   退出码 0。目标模块相关命令输出为：

   ```text
   ✔ [9940/9940] Built NSFormalization.Section3.T22.Assembly (2.5s)
   Build completed successfully (9940 jobs).
   ```

   输出中没有
   `warning: NSFormalization/Section3/T22/Assembly.lean`；旧的
   `Definition boundedDomainNorm is a proposition` warning 已消失。其余输出是 replay
   的上游依赖 warnings。

2. 正向 research probes，逐个执行：

   ```sh
   cd verification
   lake env lean ../research/T23/probes/assembly_box_closes.lean
   lake env lean ../research/T23/probes/rev484_domain_comparison.lean
   ```

   两条命令均退出码 0，输出均为 **0 bytes**。

3. 负向 research probe：

   ```sh
   cd verification
   lake env lean ../research/T22/probes/rev423_negative.lean
   ```

   退出码 1；按文件自身要求，变异结论在第 21 行被拒绝。未修改 probe。

4. 传递公理审计：

   ```sh
   cd verification
   lake env lean ../research/T22/axioms_ureg.lean
   ```

   退出码 0；其中本次声明的输出为：

   ```text
   'NSFormalization.Section3.T22.boundedDomainNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   其余 proof-bearing declarations 同样只列这三个标准公理；纯结构声明仍按预期列
   `does not depend on any axioms`。

5. 仓库 gates：

   ```sh
   make check
   make test
   make test-mutations
   ```

   三条命令退出码均为 0。`make check` 的 13 个 policy tests 全部通过且 work queue
   一致；`make test` 检查 `checkedBoundedDomainNorm` 与
   `checkedBoundedDomainNormStatement` 仍只有标准逻辑公理；mutation suite 结果为：

   ```text
   implementation_refactor: accepted
   admitted_proof: rejected as required
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   ```
