# REPORT 211 — A01 local theory bundle

## 1. 证了哪个定理

`horizon_lower_bound_H7_fixedForce`：对每个正黏性、固定 `MemForceR` 外力及
有限物理 H⁷ 范数界 K，存在一个正 δ，低于该球内所有初值的 `localHorizon'`。
`uniformHorizon_antitone` 证明柱面初值半径 R 和时间 sup 外力界 B 增大时，
所选视界不增。`manuscriptLocalRegularity_localCarrier` 为同一所选解、同一
视界提供全部四项 manuscript regularity，包含初始时刻的压力恢复。

## 2. Lean 里现在有什么

新增 `formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean`，34 个
顶层声明。`LocalCarrier` 保存 datum、U、全阶 hpairs/hpaths、velocity、
hslice/hc3、G/hG_int/hG、经典解 w，以及初值和速度识别。`localCarrier`
选择的是整个 bundle，没有丢掉 lane 209 所需的见证。

`localHorizon'` 的实际 R 是所选 smooth datum 的柱面 H⁷ 范数，B 是 `[0,1]`
上连续 H⁶ force path 的 sup 范数。连续路径的实值范数给出有限逐点界。
视界取 lane 210 两个严格 Picard 预算在 `[0,1]` 内可行时间集合上确界的一半。
正性由 vendor 正预算定理保证，集合包含关系给出反单调性；复用 lane 210
的 Picard 证明在这一指定视界构造解，而非直接使用其任意存在见证。

物理 H⁷ 到柱面半径的比较常数为
`datumRadiusConstant = ∑ j ∈ Finset.range 8, D01.jetDatumConst j 7`，由已有
`ordinarySobolev_norm_le_tensor` 和 datum→jets 估计证明。`16^m/4^m` 的既有
反向估计不用于这一方向。`localTheoryData : LocalTheoryDataShape` 可供下一
车道逐字段注册。探针完整复制 Spec 的 API 结构，验证除 H¹ 下界之外的各字段。

记录包含 attempts、A3_SPLIT 的 lane 211 行、公理审计与 API 探针。没有修改
既有 Lean 模块、Contracts、Bindings、Tests 或 contracts.json。

## 3. 缺口是什么

本次 carrier bundle、统一选择、正则性、固定外力 H⁷ 下界和数据 API 已完成。
原文 H¹ 命题仍未证明或假设。`HorizonLowerBoundH1` 已由 lane 210 占用；
新模块保留它，并以 `ManuscriptHorizonLowerBoundH1` 逐字重述该字段，绑定到
新视界，附任务要求的开放义务说明。探针验证两者定义相等。正式 V2 陈述与
合同注册仍待 owner 决定；本交付不声称完整 `LocalTheoryAPI` 已被实例化。

工作树初始处于未完成 merge 状态，worker 没有操作它；外部协调在工作期间
完成为 `9e0c8c6`。本车道提交仅包含本次六个文件的改动。未执行 merge、rebase
或 push。

## 4. 跑了什么命令、什么结果

所有 Lean shell 先 `. scripts/lean-env.sh`；Lake 仅在 `verification/` 运行，
`LEAN_NUM_THREADS=6`。

- `lake -q --log-level=error build NSFormalization.Section4.A01.LocalTheoryBundle`：
  exit 0，零输出。使用 quiet/error 参数避免既有依赖 warning 重放。
- `lake env lean` 正式模块：exit 0，零输出。
- `lake env lean ../research/A01/axioms_local_theory_bundle.lean`：exit 0；
  34 个新增顶层声明全部恰好 `[propext, Classical.choice, Quot.sound]`。
  零初值/零外力实际 bundle 及一般反单调性 examples 通过。
- `lake env lean ../research/A01/probes/local_theory_api_shape.lean`：exit 0，零输出；
  API 类型与 H¹ 原文字段定义等式通过。
- `make check`：exit 0，含 13 项 Python 测试和 30 个任务一致性检查。
- `make test-mutations`：exit 0；内部 `lake test` 通过，重构接受，三项负变异拒绝。
- `git diff --check`、禁止证明命令扫描、公理列表精确检查、Spec API 逐字比较：通过。

未新增 heartbeat 设置。原始门禁日志位于未跟踪的 `tmp/211-*.log`。
