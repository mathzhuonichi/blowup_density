# Lane 239 — 独立规格草案 B

## 1. 处理了哪个定理

完成 `cor:Rclasses` 的独立 Lean 陈述：将定理 4.1 的低于阈值稠密性、零初值 iff 和正则参考解的历史/能量附句移到 F_c、F_rd，并显式列出 Schwartz 初值特例。本任务只写规格，没有证明该推论。

## 2. Lean 里现在有什么

`DraftB.lean` 定义 `BlowupDensity.Contracts.V1.RClassesDraftB.RClassesAPI`，含 `density`、`zeroIff`、`schwartzDensity`、`regularReference` 四个字段。只导入注册合同；每字段有论文行号及量词顺序。无占位 Prop、无公理、无证明占位、无 API 实例。`COMPARISON_B.md` 给出逐条映射、环境参数/类型转换/拓扑选择与歧义。未读取指定禁读材料或另一草案；没有修改注册合同、论文、共享状态文件。

## 3. 缺口是什么

数学证明与两份独立规格的协调均留待后续。本稿不新增待注册定义。需协调的解释集中在“早期历史”“趋零”及恰时奇异的展开：本稿采用任意预定 T 前历史截止、同一见证满足任意力/能量误差，并保留末时无界速度；不额外要求跨所有 q,s 的共同插入族。紧支撑修正作为推论证明机制，结果层面由 f∈Y 表达保类，不新增支持控制字段。完整说明见对照文档。

## 4. 跑了什么命令、什么结果

- 加载 `scripts/lean-env.sh` 后，在 `verification` 中运行 `lake env lean ../research/R45/DraftB.lean`：通过，无诊断。
- `make check`：通过，包括 13 项合同政策测试和 30 项工作条目一致性检查。
- `make test`：通过，注册合同测试完成。
- `make test-mutations`：通过；实现重构可接受，证明占位、额外公理、削弱假设均按要求拒绝。此检查不是本推论的 PDE 证明。
- 首次 elaboration 发现未开放的 `Space` 被解释为自动隐式类型参数；改为注册空间的全限定名称后通过。

仅提交本 lane 的三个交付文件；不 push、merge 或 rebase。为保持双盲及交付范围，不读取或更新可能包含另一规格状态的 `NEXT_SESSION.md`。
