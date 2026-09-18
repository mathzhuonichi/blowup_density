# Lane 304-SPEC-t20-draft-b report

## 1. 证了哪个定理

本 lane 是 statements-only 双盲草案，没有添加数学证明。它精确规格化了
`paper/sections/03-torus.tex:383-503` 的 Proposition 3.7
`prop:critical`：对某个只依赖单位环面和范数约定的 `c>0`，
`ν>0`、`g∈F_T` 且 `‖g‖_{L¹_tH^(1/2)_x}<cν` 时，零初值最大解的
`maximalLifespanT` 等于 `⊤`。同时规格化了证明中的均值演化、
`eq:meanbound`、保留常输运项的 `eq:meanfree`、反自伴/乘子交换、
`eq:criticalenergy`、`eq:bintegral`、`eq:ybound`、`eq:H1energy`
以及进入 T11 continuation criterion 的平方 `H²` 可积性。

## 2. Lean 里现在有什么

`research/T20/DraftB.lean` 已可单文件 elaborate。它导入已注册的
`Contracts.V1.TorusData`，并只在原 namespace 中复制 T10 未注册的
solution-class 语汇、T11 的 local/continuation/mean-reduction API 和 T12
的 mean-zero calculus API。T20 namespace 中有显式定义
`meanPathT`、`meanFreeVelocity`、`meanFreeForce`、`constantTransportT`、
`criticalY/Z/B`、`criticalBIntegral` 和 continuation 量。

`CriticalRegularityTAPI` 以 T11 的 local/continuation/mean-reduction API 和 T12
calculus API 为索引，并采用 Type-valued house style：`c`、两个非线性吸收常数、
`H¹` Young 常数和 continuation 常数都是数据字段，在 `ν,g` 之前选定；
正性和两个 `c<1/(4C)` 字段排除空洞的小性阈值。所有范数保持
`ℝ≥0∞`；只在必须写导数的实值能量里用 `toReal`，并由
`reduction_regular` 明示保证对应范数 `≠⊤`。

`research/T20/COMPARISON_B.md` 给出了 paper clause → Lean field →
R43/C01/A04 counterpart 的逐项表，并记录表示选择、歧义、所需引理和
`Paper1/` 实现候选。

## 3. 缺口是什么

这份草案不构造 `CriticalRegularityTAPI`。主要实现缺口是：从经典周期解导出
半整数齐次范数的有限性和可微性；对未平移的 `v=u-m` 证明常输运项的反自伴与
`Λ` 交换；把 T12 临界嵌入装配成 `eq:criticalenergy`；完成标量 bootstrap；
证明 `H¹` 吸收、均值/零均值 Fourier 模正交分解，并把有限的
`squaredHTwoIntegralT` 交给 T11 `lifespanInfiniteOfLocallyFinite`。
`Paper1/CriticalEnergy*` 可复用标量 bootstrap 骨架，但
`PeriodicCriticalRegularity.CriticalRegularityCertificate` 目前把分析桥全部藏在
`global_lifespan` 字段里，不能直接实现本草案的细粒度 API。

## 4. 跑了什么命令、什么结果

- `. ../scripts/lean-env.sh && lake env lean ../research/T20/DraftB.lean`
  （在 `verification/` 中）：成功，exit code 0。
- `. scripts/lean-env.sh && make check`：成功，exit code 0；架构检查、
  contract policy tests 和 work queue 检查通过。
- `. scripts/lean-env.sh && make test && make test-mutations`：成功，
  所有已注册合同测试通过，mutation suite 通过；输出只含现有上游 linter warnings。
- `git diff --check`：收工前成功，无 whitespace 错误。
- `rg -n "sorry|admit|axiom|native_decide" research/T20 --glob '*.lean'`：
  收工前无命中。

本 lane 只新增 `research/T20/` 下的三个 deliverable，不修改已冻结合同、论文或其他 T20 lane，
并会在当前分支做本地 commit，不 push/merge/rebase。
