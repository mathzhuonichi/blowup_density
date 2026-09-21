# Lane 238 report

## 1. 规范了哪个定理

独立起草了 `cor:Rclasses`（Corollary 4.x / blueprint R45）的 Lean 陈述。
它把 Theorem 4.1 的两个阈值结论分别限制到紧支撑力类 `F_c` 和快速衰减
力类 `F_rd`，并保留定理的参考解逼近附加结论；同时显式记录快速衰减
版本对 Schwartz 无散初值 `S_σ` 的结论。本 lane 按要求只写 statement，
没有提供或声称任何证明。

## 2. Lean 里现在有什么

`research/R45/DraftA.lean` 提供 `RClassesAPI`，共有八个字段：两个力类各自
的次临界密度、零初值完整 iff、参考解/历史/能量逼近，以及快速衰减类对
`S_σ` 的密度和逼近两个显式字段。相对拓扑使用注册的
`RelativelyDense`，奇异力集合使用参数化的 `breakdownSetIn`，所以每个
逼近力都确实留在相应子类中。局部 `rClassesThreshold` 逐字表达
`2/q-3/2`；局部 `HasReferenceApproximationRider` 把初值、早期历史、精确
寿命 `T` 和 `E_T` 逼近写成完全展开的量词命题，不是占位 `Prop`。

`research/R45/COMPARISON_A.md` 给出逐条 paper-to-Lean 对照、量词和 cast
选择、相对拓扑解释、继承自 Theorem 4.1 与本推论新增的区分，以及十项
原文歧义及本稿取舍。

## 3. 缺口是什么

这是双盲 draft，尚未与另一稿比较，也未晋升为 `verification/Contracts`。
V1 Data 已注册组成参考解附加结论所需的解、`E_T`、力范数和最大寿命，
但尚无把它们组合起来的统一谓词；本稿的
`HasReferenceApproximationRider` 因而标记为 **needs registration**。
原文没有为 “same earlier history” 和 “tending to zero” 绑定显式参数，本稿
选择等价的邻域表述：任意 `S<T`、任意正的力误差和能量误差同时可达。
这一选择应在双稿 reconciliation 时重点核对。

## 4. 跑了什么命令、结果

- `. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R45/DraftA.lean`：通过，无输出。
- `git diff --check` 与对新增 Lean 文件的 `sorry/admit/axiom/native_decide`
  搜索：通过，无输出。
- `. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check`：通过；合同策略的
  13 项测试全部通过，work queue 检查通过。命令照常报告仓库既有 copied
  source admission 统计与 `source_hashes_match: false`，但整体退出码为 0，
  本 lane 没有改动这些源文件。
