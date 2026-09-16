# 268-MAINT-ledger-t10-t24 维护报告

## 1. 证了哪个定理

本 lane 不证明 Lean 定理；它把 Section 3 的 T10–T24 十五个工程节点登记为可执行的陈述任务。每个节点现在都有 §3 对应的精确目标句、数学依赖、P1/P2 优先级和起始证据；关键链为 T10 → T11 → T18 → T19 → T21，T13 与 T20 也标为 P1。

## 2. Lean 里现在有什么

没有修改 Lean、`verification/`、`research/` 或论文源码。`formalization/blueprint/tasks.json` 从 30 个节点增至 45 个，生成的 `DEPENDENCY_GRAPH.md` 含 T10–T24 全部节点和 §3 的精确边；`collaboration/work_items.json` 同步为 45 条，新增项均为 `specification`、未分配 owner、空合同列表。T10/T13 为 `needs-specification`，其余新增项为 `ready`，并生成了十五张 `collaboration/tasks/T1x.md` 任务卡和更新后的总表。

既有 DAG 没有子节点的 bucket 字段；桶由 T01–T04 上保留的 `manuscript_labels` 和未来合同的 `parent_task` 表达。因此未移动或复制桶标签，任务交付中按 §3 固定注册父项：T10–T12 → T01，T13/T15–T18 → T02，T19–T21 → T03，T22–T24 → T04；T14 保留计划表的 T01/T02 双归属，注册时按合同组件分别落桶。

## 3. 缺口是什么

十五项都还没有注册合同；下一步仍是各自的 `research/T1x/Spec.lean` 对账、评审和合同注册。检查器不接受 ledger 状态 `open`，允许态中以 `ready` 表示其余十三项的开放待领状态；已有双稿的 T10/T13 保持 `needs-specification`。

本 checkout 中 T10 的 `research/T10/DraftA.lean`、`DraftB.lean` 以及 T13 的 `COMPARISON_A.md`、`COMPARISON_B.md` 只在 263–266 lane/worktree，未合入当前树；而蓝图检查器要求每个 `evidence` 路径是当前 checkout 内的文件。为保持 `make check` 可移植且不违反“不得修改 research”，证据改用当前已跟踪的 263–266 lane briefs（其中逐字记录这些 `research/...` 路径），并直接引用当前已有的 `research/T13/RECONCILIATION.md`。

## 4. 命令与结果

- `python3 experiments/tasks.py --help`：确认 CLI 仅有 `list/show/claim/render`。
- `python3 experiments/check_formalization_plan.py`：重新生成蓝图文档与检查快照；报告 `task_count: 45`，依赖闭包无缺失 import。
- `python3 experiments/tasks.py render`：成功生成 45 项总表及十五张新增任务卡。
- 自定义只读一致性检查：十五个依赖列表逐项等于 SECTION3_PLAN §3，Mermaid 中对应节点/边齐全，十五张卡均含源合同文本，所有 DAG evidence 路径存在。
- `git diff --check`：通过。
- `make check`：exit 0。末尾输出：

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

这是工程/台账维护；按任务约束没有运行 Lean、`make test` 或 `make test-mutations`。
