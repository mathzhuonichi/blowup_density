# Lane 233 — R42 family from data

## 1. 证了哪个定理

`BlowupDensity.Bindings.insertionLifespanV2_of_data` 无额外假设地证明
R41D G1 原陈述：对 `ν,T>0`、`a∈initialClassR`、`MemForceR g`，若
`ofReal T < maximalLifespanR ν a g`，则存在合同中的 `PacketAPI ν` 与
注册的 `Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P`，且
`family.a=a`、`family.g=g`、`family.T=T`。三个等式均由构造定义化成立。

## 2. Lean 里现在有什么

新文件 `verification/Bindings/InsertionFromData.lean` 装配
A02 参考解选择 → I01 packet → I02 correction → I03 scaling → R42 family
→ V2 lifespan。另导出 `insertionFromData_lifespan` 和
`insertionFromData_forceConvergence`，将同一记录的寿命、收敛投影改写到
原始数据。审计文件 `research/R41D/axioms_insertion_from_data.lean`
覆盖全部四个实现声明，以及 `ν=T=1,a=g=0` 的两个非空洞定理：存在记录，
且合法参数 `ε=ε₀` 的插入力寿命确实为 1。六个声明的公理均恰为
`[propext, Classical.choice, Quot.sound]`。过程与失败路径记录在
`ATTEMPTS_G1.md`，`COMPARISON.md` 的 G1 已标为关闭。

## 3. 缺口是什么

G1 无数学缺口，无 I02/I03/R42 命名输入。既有 `Bindings.Packet` 与
`Bindings.Scaling` 的 `navierStokesResidual_eq` 全名冲突，不能同时导入；
本文件用新名字 `insertionFromData_packet` 重用前者上游见证并复制其字段
装配，避免修改已有模块。将来若修复既有桥定理重名，可去掉这段重复。
因此新文件也不应与 `Bindings.Packet` 同时导入，直到该既有冲突修复。
本 lane 不改已有 Lean 文件、Bindings、Tests 或合同注册表；只按要求更新
既有 `COMPARISON.md`。R41D 其他 gap 不属本次关闭范围。

## 4. 跑了什么命令、什么结果

所有 Lean 命令先加载 `. scripts/lean-env.sh`，设置
`LEAN_NUM_THREADS=6`；直接 Lake 命令从 `verification/` 运行。

- `lake build Bindings.InsertionFromData`：成功。Lake 库名是 `Bindings`，
  不是 Lean 命名空间 `BlowupDensity.Bindings`；新模块无 warning，构建日志
  仅重放已有依赖的 warning。
- `lake env lean Bindings/InsertionFromData.lean`：退出 0，输出 0 字节。
- `lake env lean ../research/R41D/axioms_insertion_from_data.lean`：退出 0，
  六个声明均只有指定三公理，两个具体实例通过。
- `make check`：退出 0；13 个合同政策测试通过，30 个工作项一致。
- `make test`：退出 0；现有注册合同闭包编译通过。新文件未注册为新合同，
  因此由上面的显式 build/direct Lean 单独覆盖。
- `make test-mutations`：退出 0；实现重构被接受，admission、新公理、削弱
  假设三个变异均按预期拒绝。
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`：
  退出 0，基线兼容检查通过。
- `git diff --check`：通过。新增 Lean 文件没有禁用证明占位或心跳覆盖。

本分支本地提交；不 push、merge 或 rebase。原始门禁输出留在本 worktree
的 gitignored `tmp/*_233.log`。
