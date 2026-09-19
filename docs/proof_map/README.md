# Sections 3–4 proof map

`index.html` 是单文件离线中文导读：CSS、JavaScript、SVG、55 份合同数据均内联，不发出外部请求。页面面向不熟悉 Lean 的读者，区分论文目标、依赖关系、已注册合同、证明/合同架构、历史构建证据和 owner-pending 范围。

## 提取快照

内容提取时的 `git rev-parse HEAD`：

```text
7e10508b9d5f3e07dbdbc6d493b0a0ef558b7712
```

这是完成页面六个正文段落后的提交；随后只增加本 README、维护报告及纯文档验收修正。页面中的构建数据来自所列历史报告，不代表在 lane 490 重新运行 Lean。

主要提取命令（从仓库根目录执行）：

```sh
# 合同总数、分节和逐行数据
jq '.contracts | length' verification/contracts.json
jq -r '.contracts | group_by(.parent_task)[] |
  [.[0].parent_task, length, (map(.id + "@v" + (.version|tostring)) | join(", "))] | @tsv' \
  verification/contracts.json
jq -c '[.contracts[] |
  {i:.id,v:.version,p:.parent_task,m:.specification,
   s:(.scope|gsub("[\\n\\r]+";" ")|split(". ")[0])}]' \
  verification/contracts.json

# 每个节点的静态规模；declaration header 不是 kernel 声明总数
for d in formalization/NSFormalization/Section{3,4}/*; do
  find "$d" -type f -name '*.lean' | wc -l
  rg -n '^(theorem|lemma|def|structure|class|abbrev|instance|noncomputable def)\b' \
    "$d" -g '*.lean' | wc -l
done

# 实际跨节 import 和来源引用
rg '^import .*Section4' formalization/NSFormalization/Section3
rg -n 'I01|I02|I03|R42' research/T*/RECONCILIATION.md research/T23/T23_SPLIT.md

# 页面大小、脚本语法和内嵌合同数据
wc -c docs/proof_map/index.html
perl -0777 -ne 'while(/<script>(.*?)<\/script>/sg){print "$1\n"}' \
  docs/proof_map/index.html | node --check
perl -0777 -ne 'if(/<script id="contract-data" type="application\/json">(.*?)<\/script>/s){print $1}' \
  docs/proof_map/index.html | jq 'length, (map(.i)|unique|length)'
```

合同数据的嵌入 JSON 还与同一条 `jq` 生成结果做了排序后 `diff`，结果为空；因此 55 个 id、版本、parent、模块路径与 scope 首句不是手抄副本。

## 页面数字到来源

下表覆盖页面上的数据性数字。流程图的 `1…7`、章节 UI 的 `01…06` 只是阅读顺序；合同 scope 内的行号、版本、指数和字段数全部是 `contracts.json` 原字段首句的一部分，由“55 行合同数据”这一行统一溯源，不构成页面另行推导的数字。

| 页面数字或数字组 | 含义 | 仓库来源 |
|---|---|---|
| `55 = 37 + 18` | 全 registry 合同；第 4 节 / 第 3 节 | `verification/contracts.json`；对 `id` 是否以 `T` 开头分组，结果 37 / 18；`logs/SECTION3_BUILD_20260919i.md:296-301` 复核 55 |
| `400 = 206 + 194` | 两节源码模块，分别构建，不是一条 400-target build | `logs/SECTION4_FULL_BUILD_20260917.md:28-41,55-64`；`logs/SECTION3_BUILD_20260919i.md:15-48` |
| `0 sorry/admit` | 注册闭包及两节交付源码的历史审计口径 | `logs/SECTION4_FULL_BUILD_20260917.md:192-210`；`logs/SECTION3_BUILD_20260919i.md:49-77,303-318`。不声称整个 vendor/research 树零占位 |
| `3` | 唯一允许的传递公理 | `research/MAINT/section4_pr259_body_snapshot_20260919.md:3`；`logs/SECTION3_BUILD_20260919i.md:313-314`：`propext`, `Classical.choice`, `Quot.sound` |
| `s < 1/2`, `s ≥ 1/2`, `−1/2` | L¹ 临界阈值与 L² 全空间阈值 | `paper/sections/04-whole-space.tex:7-16,31-43,78-89,136-144`；`paper/sections/03-torus.tex:6-20,349-356,383-390,506-520` |
| Theorems `4.1–4.7` | 第 4 节七个主结果和合同对应 | `research/MAINT/section4_pr259_body_snapshot_20260919.md:5-13`；论文标签见 `paper/sections/04-whole-space.tex` |
| 图中 Section 4 节点依赖 | I/A/data/closing chains | `formalization/blueprint/DEPENDENCY_GRAPH.md:1-142`；`archive/section4/PLAN_SECTION4.md:35-61` |
| 图中 `T10–T24` 与关键路径 | Section 3 DAG | `collaboration/SECTION3_PLAN.md:31-56` |
| 图中跨节虚线 | 直接 import、binding 消费或 reconciliation 明示的同骨架迁移 | `formalization/NSFormalization/Section3/T*/` 的 import；`research/T*/RECONCILIATION.md` §4；`research/T23/T23_SPLIT.md:13-17,220-246` |
| 图中每个 `modules / declaration headers` | 当前源码目录的静态文件数与指定 header 正则命中数 | 上节所列 `find` / `rg` 命令；R45/R46/R47/G01 的数来自对应 `verification/{Contracts,Bindings,Tests}` 文件集合 |
| 图中 PR 号 | 代表性 spec/proof/registration 合入，不是穷举 | `research/MAINT/section3_pr_body_snapshot_20260919.md:5-25`；`research/MAINT/section4_pr259_body_snapshot_20260919.md:5-13`；`logs/AGENT_RUNS.csv` |
| 合同表 55 行中的 id、version、parent、module、scope 数字 | 注册表原数据；scope 取首句 | `verification/contracts.json:1-610`；生成和一致性检查命令见上 |
| `206 / 206`, `232 s`, exit `0`, error `0`, `10,636` jobs, `37` contracts | 第一次 Section 4 真重编与门禁 | `logs/SECTION4_FULL_BUILD_20260917.md:47-64,227-244` |
| `205 → 206` | 旧 pathspec 漏掉根层 `HeliCorgiPort.lean` 的口径修正 | `logs/SECTION4_FULL_BUILD_20260917.md:28-33` |
| `219.648 s`, `74` warnings、其中 Section 4 自身 `2` 条 | 独立第二次 Section 4 重编 | `logs/SECTION4_FULL_BUILD_20260917_ASTRA.md:23-56,231-255` |
| `194 / 194`, `148.65 s`, exit `0`, error `0`, `.olean 194` | Section 3 真重编 | `logs/SECTION3_BUILD_20260919i.md:15-48` |
| `108` warning 行、Section 3 自身 `1` 条、grep `17` 个 sorry 文本 | Section 3 日志的 warning / 注释口径 | `logs/SECTION3_BUILD_20260919i.md:46-77` |
| `67` standard-axiom lines、`55` contracts | `make test` 与 registry gate | `logs/SECTION3_BUILD_20260919i.md:292-301` |
| gate 时间 `10.42 / 6.96 / 13.61 / 5.06 s` | Section 3 四道本地门禁 | `logs/SECTION3_BUILD_20260919i.md:294-301` |
| `384 = 335 + 49` | probe/公理扫描文件：正向退出 0 + 预期负例失败 | `logs/SECTION3_BUILD_20260919i.md:303-318` |
| `2,309`、其他公理 `0` | 扫描出的公理列表全部标准 | `logs/SECTION3_BUILD_20260919i.md:309-318,374` |
| T17 `G4/G5`、T23 `G0/G1`、`D.ε₀=0` | owner-pending 措辞及已知假陈述的反例 | `logs/SECTION3_OWNER_DECISIONS_20260919.md:5-11` |
| PR `#259`, `#270`, `#451`, `#453` | 合并顺序、最终 T23 注册和已修 defProp | `PLAN.md:4,251`；`NEXT_SESSION.md:37-38,81-89` |
| CI 本地替代日期/记录中的 lane 数字 | Actions 账单/额度阻塞时的验收政策 | `archive/section4/NEXT_SESSION_SECTION4.md:195,206-207,225`；它们是历史记录，不是云端绿灯 |

## 口径说明

- 页面所有“通过”都附带对象：模块 build、注册合同测试或 probe 扫描；不把缓存回放称为重编，也不把预期负例失败称为普通通过。
- `declaration headers` 是可复现的源码规模近似值，不是 Lean environment 内声明总数。
- PR 状态来自 2026-09-19 的仓库快照；页面没有访问 GitHub 核对实时状态。
- HTML 没有运行 Lean，也不提供比冻结合同更宽的数学承诺。
