# 267-MAINT-archive-section4 维护报告

## 1. 移动了什么

通过 `git mv` 原样归档：根目录 PLAN → `PLAN_SECTION4.md`、NEXT_SESSION → `NEXT_SESSION_SECTION4.md`、collaboration/HANDOFF → `HANDOFF_SECTION4.md`，以及 119 份 lane ≤262 的简报（含 fix/resume/review_notes 补充）。共 122 个移动文件与基线逐字节一致，未加 banner。263–266 简报留在原位，内容不变。

[归档 README](README.md) 提供完整索引：冻结交付分支 `erenup/integration`、PR #259 → main、37 个注册合同及仍在原位的 `research/<ID>/`。历史文件内路径不重写，README 说明原路径基准。

## 2. 新实时文档包含什么

- PLAN：10 行状态页头、T10–T24 DAG 与 S3-0…S3-3 规划链接、§8 六列表格；表头/分隔行及 263–266 行逐字保留。原表没有 267 行，因此新增本维护 lane，下一号 268，全局唯一；不沿用旧快照对 267/268 spec 的预指派。
- NEXT_SESSION：S3-0、T10 A 完成/B 重启后仍在写、T13 双稿与 reconciliation 完成；下一步 T10 reconciliation → T10 spec → T13 spec → 注册 `T01.torus_data`；分节分支、Section 4 owner 待办单行归档指针。
- HANDOFF：S3-1 的 T13/T16/T12/T14/T22 和 S3-2 的 T11/T20 共七行，每行给出领取条件；外部 300–399 预留，编号仍由 lead 分配。
- CLAUDE、SECTION3_PLAN 页头与 README 指向实时入口和归档；CLAUDE 当前目标、分支流程及关键路径同步改为 Section 3。

## 3. 保持不变的内容与原因

`tasks.py --help` 与源码仅支持 `list/show/claim/render`；无完成状态命令、无新增命令。校验器接受的完成态是 `merged`（没有 `done`/`complete`），但 CLI 不能设置它。因此所有 Section 4 状态及 `work_items.json` 保持原样，不把 `claim` 当作完成命令，也不手改 JSON。执行 render 后生成文件无差异。

T10–T24 未加入台账：CLI 无新增能力；且 render/check 要求台账 ID 与 `formalization/blueprint/tasks.json` 完全相同，当前仅有 T01–T04 桶。lead 后续需在获准的工程 lane 中补完成/新增命令，按注册合同及实际交付核对 Section 4 节点后设置 `merged`；为空合同列表的 reference/compatibility 节点单独核对完成证据。

新增 T10–T24 时需同步 DAG 的 `id/title/priority/contract/dependencies/evidence` 和台账的 `id/kind/state/owner/contracts/deliverable`。SECTION3_PLAN §3 给出目标、依赖与桶映射，§6 给出编号/状态和合同前缀规则，未给出完整可直接导入的字段记录；lead 需审定这些字段（尤其 T14 的 T01/T02 归属），按实际依赖分配状态，不把全部节点直接标 ready。合同 parent_task 保持 T01–T04 桶。

本次没有修改任何 Lean、verification/、formalization/、research/、paper/、logs/AGENT_RUNS.csv 或 logs/LESSONS.md；没有运行 lake。历史文档保留原内容和历史相对路径，受保护文件中的历史提及未改。工作仅在本 worktree；未 push、merge、rebase，未操作冻结分支。`tmp/plan_row.py` 本 worktree 不存在；已按原表逐字检查表头及每行六列兼容性。

## 4. 命令与结果

- `python3 experiments/tasks.py --help`：仅 list/show/claim/render。
- `python3 experiments/tasks.py render`：成功，生成物无差异。
- `rg -n 'HANDOFF\.md|NEXT_SESSION\.md|PLAN\.md' --glob '*.md' --glob '!archive/**' .`：检查实时入口及历史引用；结果留在本地 `tmp/link-audit267.txt`。
- `python3 tmp/verify267.py`：122 个归档文件逐字节一致、263+ 简报未改、台账未改、五条六列 lane 行及禁止路径检查全部通过。
- `make check > tmp/check267.log 2>&1`：exit 0。末尾输出：

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

这是架构/台账检查结果，本次未执行 Lean 编译。
