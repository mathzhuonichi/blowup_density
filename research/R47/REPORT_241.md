# Lane 241 — R47 draft B

## 1. 陈述了哪个定理

独立写出 Theorem 4.7（`thm:Rgrid`，`04-whole-space.tex:297–303`）的 Lean 陈述：对预先固定的有限网格族，选择同一个插入家族，使所有单元的速度与力平均在 `0 ≤ t < T` 相等，同时最大寿命恰为 T，能量与力范数收敛，并具有共同球内支撑。此次仅做 specification，没有证明该定理。

## 2. Lean 里现在有什么

`DraftB.lean` 中的 `RGridFamily` 逐条记录结论，`RGridAPI.choose` 表达先固定参考解和网格族、再选择共同家族的量词顺序。只直接 import `Contracts.V1.Data`；网格、单元和观测映射均已注册，无需新增待注册定义。使用原始 `ClassicalSolutionR` 家族，理由及逐条对应表见 `COMPARISON_B.md`。没有占位 Prop、公理或未完成证明。

## 3. 缺口是什么

本次交付不包含结构体的 inhabitant、绑定、注册或证明。待双盲比对确认的解释点：参考解延拓余量采用已注册的半开区间约定；球的闭包位于单元内部；压力允许依赖时间的空间常数规范；用原始解数据而非预选的 `InsertionFamilyAPI` 表达存在性。没有阅读另一草稿、受禁的陈述汇编、R47 相关既有文件或 collaboration briefs。下一步由独立比对负责人审阅；本 lane 不推送、合并或 rebase。为保持双盲范围，会话交接记录写在本报告，不读取或修改共享 `NEXT_SESSION.md`。

## 4. 跑了什么命令、什么结果

已执行 `. scripts/lean-env.sh`，然后在 `verification/` 下执行 `lake env lean ../research/R47/DraftB.lean`：退出码 0，无诊断。`make check`、`make test`、`make test-mutations` 均退出码 0；mutation suite 通过。`make test` 回放既有依赖的警告，但没有失败。检查日志在 gitignored 的 `tmp/lane241/`。`git diff --check` 通过。所有交付文件随本报告在当前 lane 分支提交。
