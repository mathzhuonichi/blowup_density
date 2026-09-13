# LESSONS.md — 坑与经验（滚动更新；每条一行，新的加在最上面；日期 = 学到的那天）

- 2026-09-13 续用原 worker 改 review 意见（SendMessage 回同一个 agent）：9 分钟、17 次工具调用；新开一个要 30–45 分钟。review 后先想"能不能续用"。
- 2026-09-13 同一 worktree 里并发两个 lake 会弄坏 `vendor/.lake/build`（缺 olean、瞬时竞态）；lake 的锁挡不住。一个 worktree 一次一个 lake；安装脚本的 `lake test` 没跑完别自己起 build。
- 2026-09-13 每条新 lane 的固定成本曾是约一小时（重编 formalization + vendor 闭包）；`lean-install.sh` 现在从根复制编译产物，lake 只重编改动的。开小任务前先看固定成本。
- 2026-09-13 `structure` 型的合同定义（`ClassicalSolutionR`）本地重述是另一个类型，`rfl` 桥不可能；逐字段转换双向可 typecheck（reviewer 验证）；本地重述只留一份，其它模块 import。
- 2026-09-13 同一节点两条车道并行（032/033）会各自重述同一块定义 → 合入时要去重。同一时间一个节点只开一条改代码的车道；spec 车道可并行。
- 2026-09-13 在 `formalization/` 下跑 lake = 重新 clone + 从源码编 Mathlib（worker 一次、lead 一次）。hook `guard.py` 已拦；软链防护已加。
- 2026-09-13 `pkill -f <模式>` 会匹配到自己的 shell 命令行（exit 144）。用 `pgrep -f '^/exact/path'` 再 kill。
- 2026-09-13 任务卡上的"证据"两次都不是对的定理（A04 的 `ScalarEnergyContinuation` 是 36 行转发；A02 卡片没提最合适的 `classical_uniqueness_on_Icc`）。spec 车道必须自己 grep 三个源码库。
- 2026-09-13 Mathlib 没有连续变系数 Grönwall（只有常系数与离散版）；A04 G3 要自建。
- 2026-09-13 树里全部 8 个全空间能量定理都假设紧支（对 X_R 不成立）；C01 要在 `SmoothL2Field` 层重建，不能复用。
- 2026-09-13 CI：2 核 runner 冷 `lake test` 78 分钟；120 分钟上限被掐；缓存只在成功时保存 → restore/save 拆开、`if: always()`、180 分钟。合并一批 PR 后只有最后一轮 CI 有意义（cancel-in-progress），记账 push 攒到 CI 结束。
- 2026-09-13 `gh pr merge` 在 force-push 后 10–30 秒内报 "not mergeable"；轮询 `mergeable` 到 `MERGEABLE` 再合。
- 2026-09-13 `tasks.py render` 整文件覆盖任务卡；Attempts 只放 `research/<ID>/ATTEMPTS*.md`（hook 已拦手改）。
- 2026-09-13 spec 里"能被错误实现满足"的字段形态：常数在数据之后选、量词顺序、缺 `0 < lifespan`、S 超出寿命范围、`Ioo` vs `Ico`、`ℝ≥0∞` vs `ℝ`、区间积分的 junk value。reviewer 清单里逐条问。
- 2026-09-13 D01 草稿 A 的 F_R 漏 C^∞ 让定理 4.1(ii) 变假：两份盲稿比对抓到。合同 spec 一律两份盲稿。
- 2026-09-13 合同不能 import `NavierStokes.*`：先内联 20 个定义 + rfl 桥，再把政策放宽为 7 模块白名单（政策变更单独交 owner）。
- 2026-09-12 `lake build -j` 在此版 Lake 无效，用 `LEAN_NUM_THREADS`；5 条车道各 6 线程。
