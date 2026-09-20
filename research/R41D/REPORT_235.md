# Lane 235 — Theorem 4.1 density for F_R

## 1. 证了哪个定理

证明 `breakdownDenseR_of_subcritical`：ν,T>0、q∈{1,2}、
s < 2/q.toReal − 3/2 时，每个 a∈initialClassR 都满足
`Data.BreakdownDenseR ν a T q s`。这正是 thm:Rmain (i)。
`breakdownDenseR_zero_of_subcritical` 给出 (ii) 的 if 方向。
阈值直接由 `ThresholdAPI.formula` 改写，没有更改陈述。

## 2. Lean 里现在有什么

新增 `verification/Bindings/DensityFromInsertion.lean`：三个声明，包含
对任意 q,s 的零力范数恒等式，以及一般初值、零初值稠密定理。
证明按论文分两情形：已有 breakdown 时取原力；否则由 lane 233
取得同一 V2 插入记录，从右邻域收敛选合法 ε，利用力类保持与精确寿命。
`research/R41D/axioms_density.lean` 审计三个实现和两个具体定理；
五者均恰为 `[propext, Classical.choice, Quot.sound]`。
另有 ν=T=1、a=g=0、q=1、s=0、半径 1 的非空洞 example。
过程记录见 `ATTEMPTS_DENSITY.md`，字段状态已补到 `COMPARISON.md`。

## 3. 缺口是什么

本任务的 F_R 稠密结论无额外分析前提。基线上只有 q=1 非稠密模块；
只读 lane 232 分支可见 q=2 的 `NonDensityL2.lean`，但未引入，故不声称
双向 iff；only-if 属于 224/229/232。未装配研究版 RDensityAPI 的加强
见证字段，也不处理 compact/rapid 类。继承 lane 233 的 import 限制：
不可同时 import `Bindings.Packet`，原因是既有 Packet/Scaling 声明重名。
没有修改已有 Lean 模块、Bindings、Tests 或注册表。

## 4. 跑了什么命令、什么结果

先 `. scripts/lean-env.sh`，Lean 使用 `LEAN_NUM_THREADS=6`，所有直接
Lake 命令均从 `verification/` 运行。

- `lake build Bindings.DensityFromInsertion`：成功；新模块无警告，日志有
  既有依赖警告重放。
- `lake env lean Bindings/DensityFromInsertion.lean`：退出 0，输出 0 字节。
- `lake env lean ../research/R41D/axioms_density.lean`：退出 0，五条标准三公理。
- `make check`：通过，13 个政策测试及 30 个工作项一致性检查成功。
- `make test`：通过，已注册合同闭包编译成功。
- `make test-mutations`：通过，重构接受，三个违规变异按预期拒绝。
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`：通过。
- `git diff --check`：通过；无证明占位、额外公理或心跳覆盖。

新模块由显式 build/direct Lean 覆盖，未新增合同注册。日志在本 worktree
的 ignored `tmp/*235.log`。仅在当前分支本地提交；未 push、merge 或 rebase。
