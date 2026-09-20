# Lane 243 — 四段报告

**1. 陈述了什么。** 完成 Proposition 4.6 (`04-whole-space.tex:218-228`) 的独立 draft B；本任务只写陈述，没有证明该命题。涵盖两个完整 Bochner 空间中的爆破紧支光滑力密度，以及同一个插入族上的强能量轨道收敛和三种力范数同时收敛。遵守双盲限制，没有打开另一草稿或被禁止的研究文件；允许合同中的交叉引用未追读。

**2. Lean 里现在有什么。** `research/R46/DraftB.lean` 定义 `BlowupDensity.Contracts.V1.REnergyDraftB.REnergyAPI`，含 `sobolevDensity`、`homogeneousDensity`、`strongTrajectoryClosure` 三个字段。密度统一复用 `CompletedDenseVia`，分别指定 `IsSobolevPath s` 与 `IsHomogeneousPath (-1)`。轨道字段先量化参考解和球，再存在性选择一个 `InsertionFamilyAPI`，同时要求经典解、力属于 F_R、寿命等于 T，以及两个极限。全部直接 import 都是 `Contracts.V1`；没有新增公理、证明占位或未定义的 Prop。无需新增局部定义。`COMPARISON_B.md` 记录逐条对照、量词顺序、实现选择及歧义。

**3. 缺口是什么。** 这是可 elaboration 的规格类型，不是其 inhabitant。后续证明仍需齐次完成空间的组装和同族齐次缩放估计。需合审的陈述选择是：用 H⁰ 范数表示 L²；将 “regular through T+δ” 显式保留为 `RegularThrough`；携带注册插入族的构造见证，另补其缺少的经典解和寿命结论。没有对粗糙背景力定义经典爆破，也没有假设背景属于齐次空间。

**4. 命令与结果。** source `scripts/lean-env.sh` 后，`cd verification && lake env lean ../research/R46/DraftB.lean` 通过，无诊断；`make check`、`LEAN_NUM_THREADS=6 make test`、`make test-mutations` 均退出 0。变异检查接受等价重构，按预期拒绝 admission、额外公理、弱化假设。`make check` 的既有源快照摘要显示 `source_hashes_match: false`，但该检查整体退出 0；本 lane 未修改源快照或已注册合同。测试与变异日志在 `/tmp/243-spec-test.log`、`/tmp/243-spec-mutations.log`。提交到当前 `erenup/243-SPEC-r46-draft-b` 分支，不 push、merge 或 rebase。
