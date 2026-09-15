# 2026-09-15：恢复 lane 158 / 160

## 1. 证明范围与云端基线

本轮先通过 GitHub 核对仓库状态：PR #15 已合入 `main`，本地与云端基线均为
`da640be`。云端 `PLAN.md` 与该提交中的文件一致，无开放 PR。
暂停记录中的 lane 158 提交 `47cf101` 仍在远端分支，本轮恢复其源文件，
补齐记录中指出的顶阶和时间连续性两项；lane 160 从头实现。

本轮通过 `codex/158-160-formalization-resume` 向 `main` 提 PR。
原 `research` 工作区的无关修改未纳入本仓工作。

## 2. Lean 中新增内容

- A01 `ConstructorPieces`：从角不变的柱面路径获得所有 `m ≤ q+1` 阶的
  弱导数和候选速度切片的 Sobolev datum；每个空间导数词都有连续的普通 `L²` 路径。
  旧证明的 `m+3 ≤ q+1` 限制消除。顶阶 `q=6, m=7` datum 和 `n=7` 路径用于消费检查。
- A04 `ForceShift`：正向时间平移不增大半直线上的外力 `L¹_tH^s_x` 范数。
  逐个平移 Sobolev datum 后比较定义中的下确界，不需要另加 `MemForceR`。
- A04 `Continuation`：从短区间解族构造最大解场，将一致重启界传到终点；
  `restartBeyond` 保留完整的 `S+δ`，且 δ 在初值、外力和终点之前选定。
  再合并速度、紧区间外力、外力时间积分三项有限界，得到 `extendsBeyond` 和
  `lifespanInfiniteOfLocallyFinite` 的条件装配。

## 3. 仍然缺什么

A01 的联合光滑性、共同时间区间上的全阶正则性、datum 范数连续性、散度和压力
装配，以及与原始初值/外力的同定仍未闭合。`CarrierConstructorFull` 是明确列出
局部理论全部输出的研究目标，消费探针并不证明该目标本身。

A04 最终 `restartBeyond` 仍假设精确的 A02 `Restart`；最终无限寿命结论还假设
精确的 G3 `HigherOrderBound`。本轮没有证明这两项分析输入，也没有把条件定理
注册成无条件 PDE 合同。现有 26 条合同、绑定和测试保持原样；论文第 4 节
定理/命题 4.1–4.7 的整体形式化尚未完成。

后续顺序仍以主计划为准：A01 B1/B2 构造子和 A3 主链；A04/G1 注册、C01 E5–E7、
A05 U1–U7、R43 G7。新条件装配可在上游输入闭合后直接消费。

## 4. 验证与分工

按用户指定，A01/A04 代码分别由 `gpt-6-astra` low 子代理编写；所有 Lean 编译和
现有验证套件由 `gpt-5.6-luna` high 子代理运行。主代理复核 A01 源码，A01 编写者
独立复核 A04 源码；审查记录在各自 `research/` 目录。

本机环境为 `.elan/env.ps1`、Lean `4.34.0-rc2`、`LEAN_NUM_THREADS=1`，所有 `lake`
从 `verification/` 运行。复用预编译缓存，对新增依赖按需补编。

本地检查（全部由 Luna 执行；Python 脚本使用实际可用的解释器）：

| 检查 | 结果 | 本地日志（`tmp/`） |
|---|---|---|
| `lake build NSFormalization.Section4.A01.ConstructorPieces` | exit 0 | `compile_final_A01_ConstructorPieces_20260915.log` |
| `lake build NSFormalization.Section4.A04.ForceShift` | exit 0 | `compile_final_A04_ForceShift_20260915.log` |
| `lake build NSFormalization.Section4.A04.Continuation` | exit 0 | `compile_final_A04_Continuation_20260915.log` |
| `lake env lean`：A01 axioms、`ctor158_datum`、`ctor158_full` | 全部 exit 0；标准三公理 | `probe_final_A01_*_20260915.log` |
| `lake env lean ../research/A04/axioms_r1c1.lean` | exit 0；9 项标准三公理及 4 个正例 | `probe_final_A04_axioms_20260915.log` |
| `check_formalization_plan.py --check`、`check_contracts.py`、`check_work_queue.py` | 全部 exit 0 | 各检查的 `20260915` 日志 |
| `test_contract_policy.py` | 13 项通过，exit 0 | `test_contract_policy_final_autocrlf_false_20260915.log` |
| `check_contracts.py --base-ref origin/main` | exit 0；基线兼容 | `check_contracts_base_origin_main_20260915.log` |
| `lake test`（在 `verification/`） | exit 0；26 条合同仅标准三公理 | `lake_test_final_20260915.log` |
| `test_contract_mutations.py --skip-build` | exit 0；重构接受，补洞/额外公理/弱化假设均拒绝 | `test_contract_mutations_final_skip_build_env_20260915.log` |

Windows 测试环境说明：本仓 `core.autocrlf=false`，系统 Git 配置却为 `true`。
保护测试创建的临时仓库继承系统设置，初次运行有 4 项因 CRLF/LF 字节差异失败。
仅在该测试进程通过 `GIT_CONFIG_COUNT=1`、`GIT_CONFIG_KEY_0=core.autocrlf`、
`GIT_CONFIG_VALUE_0=false` 匹配本仓配置后，13 项全部通过。未修改测试代码、
字节比较断言或全局 Git 配置。`make` / `python3` 别名在本机不可用，故执行了
`make check` 对应的四项原始 Python 脚本。

变异测试初次调用未加载 `.elan/env.ps1`，因找不到 `lake` 退出；加载现有环境后
原命令全部通过。三个新增 Lean 模块未加入 `sorry`、额外公理或 `native_decide`。

云端 `main` run `34922570431` 的 architecture job 因账户账单/额度未启动，
lean-contracts 被跳过。这是外部 CI 限制，不作为本地验证成功的证据。
