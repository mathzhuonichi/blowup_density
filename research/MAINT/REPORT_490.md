# REPORT 490 — Sections 3–4 proof-map HTML

## 1. 页面包含什么

完成一个中文、离线、响应式的单页证明地图。页面依次给出全空间与环面论文目标、可点击/可缩放/可拖动的手工 SVG DAG、由 `verification/contracts.json` 生成的 55 行可筛选合同台账、paper → Spec → canonical proof → frozen contract → binding → axiom test → registry 架构、两节历史全量构建与门禁数字，以及醒目的 owner-pending 范围框。图节点面板列出通俗含义、论文标签、合同与版本、Lean 位置、代表 PR、静态规模和 caveat。

## 2. 文件

- `docs/proof_map/index.html`：约 80 KB；CSS、JavaScript、SVG 与合同数据全部内联，无外部请求。
- `docs/proof_map/README.md`：数据提取命令、提取 commit、数字到来源表与口径说明。
- `research/MAINT/REPORT_490.md`：本四段交付报告。

只修改以上三个交付文件。工作树中已有的未跟踪文件 `collaboration/briefs/cont_490-SPEC-proof-map-html.md` 没有读取、修改或纳入提交。

## 3. 未核实、未声称与显式限制

请求列出的核心数字均在仓库来源中核实，没有把无法核实的数据伪装成结论。页面没有查询远端 GitHub，因此 #259 / #270 写的是 2026-09-19 本地快照状态，不是实时状态；没有重跑 Lean，构建结果明确标成历史报告。`0 sorry` 限定为交付源码/注册闭包的审计口径，不扩张到整个 vendor/research 树。400 模块是两次分节构建之和，不宣称存在一次统一 400-target build。

页面显式保留：A01/A04 的 H⁷ 固定外力 V2 与开放 H¹ 论文句子；R47/R46 的 L¹L² 词汇差异；T17 G4 amended block 与 G5 slab bridge；T23 G0 的存在式修复（原 universal-cutoff 版本为假）和 G1 的 `IBP Ω` 条件；Prop/Type 与 domain record 约定；云端 CI 账单/额度阻塞；PR 合并顺序。Section 4 独立报告里的 combined-import 同名声明维护提示也没有隐藏。

## 4. 运行了什么

只做读取和文档验收，没有运行 Lean build。使用 `jq` 提取/分组 55 个合同；用 `find` 统计模块、`rg` 统计声明 header 与实际 imports；用论文、reconciliation、PR 快照、构建日志和 owner-decisions 日志逐段核数。使用 `git diff --check`、`node --check` 验证补丁与内联 JavaScript；将内嵌合同 JSON 排序后与 `contracts.json` 的同一 `jq` 投影做 `diff`（55 项、55 个唯一 id）；用 headless Chrome 从 `file://` 打开页面、执行脚本和生成桌面/手机截图；检查最终文件尺寸低于 400 KB，并扫描外部 URL。按用户要求未运行任何 Lean 命令、未 push、未 merge、未 rebase。
