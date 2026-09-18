# Lane 303 — T20 draft A report

## 1. 证了哪个定理

本 lane 只做陈述、不做证明。`DraftA.lean` 精确陈述论文 Proposition
`prop:critical`：存在只依赖单位环面和范数约定的 `c>0`，使每个
`ν>0`、`g∈forceClassT` 在
`‖g‖_{L¹(0,∞;H^{1/2})}<cν` 时满足
`maximalLifespanT ν 0 g = ⊤`。同一接口还陈述六个指定的证明显示式：
`eq:meanbound`、`eq:meanfree`、`eq:criticalenergy`、`eq:bintegral`、
`eq:ybound`、`eq:H1energy`。

## 2. Lean 里现在有什么

- `research/T20/DraftA.lean`：可 elaboration 的 statement-only 草案。
- 直接使用已注册 T01 `Contracts.V1.TorusData` 的 Fourier 数据、均值、
  齐次/非齐次扩展范数；只复制尚未注册且实际使用的 T10/T11/T12 声明，
  保留原 namespace、名称和源行 marker。
- 明确定义 `meanPathT`、未平移的 `meanFreeVelocity`、`meanFreeForce`、
  `constantTransportTerm`，以及 `criticalY`、`criticalZ`、
  `criticalBRate`、完整/部分 `B` 积分和 H¹ 能量量。
- `CriticalRegularityTAPI : Type` 把 `c,C₀,C₁,CH1` 作为先于所有 PDE
  量词的数据；所有扩展范数都有输入类、具体 homogeneous membership，
  或能强制有限性的估计保护。微分式只在相应范数已证明非 `⊤` 后使用
  `.toReal`，并提供真实的 `HasDerivAt` witness。
- `research/T20/COMPARISON_A.md`：逐条 paper → Lean → R43/C01/A04
  对照、设计选择、歧义、needs-a-lemma 清单和 `Paper1/` 实现候选。

## 3. 缺口是什么

这是 API 草案，主要证明缺口是：把 T11 的 data-defined mean reduction
专门化到未平移的 `u-m`；常输运与 Fourier 乘子交换及其 L² 反自伴；
从 T10 classical slices 构造 T12 的半整数 homogeneous data；由 T12 两组
临界嵌入组装 `C₀,C₁` 和两个能量恒等式；实例化已有 scalar critical
bootstrap；积分 H¹ 估计并用 `hTwo_le_laplacian`、均值/零模正交得到
T11 `squaredHTwoIntegralT` 有限；最后调用 T11 continuation API 得到
全局 lifespan。完整拆分见 `COMPARISON_A.md` 的 “Needs a lemma”。

需 reconciliation 决定的两点是：是否把论文 `:460-464` 的临界耗散
显示式另列字段，以及是否把 `:496-500` 的未编号 continuation bound
另列字段。Draft A 按简报的精确字段清单把二者都留作导出引理。

## 4. 跑了什么命令、什么结果

- `cd verification && . ../scripts/lean-env.sh && lake env lean ../research/T20/DraftA.lean`：通过，零输出。
- `rg -n '\b(sorry|admit|axiom|native_decide)\b' research/T20/DraftA.lean`：无匹配。
- `git diff --check`：通过。
- `. scripts/lean-env.sh && make check`：退出码 0；合同政策 13 个测试通过、
  work queue 一致。输出仍报告基线已知的 `Paper1/BoundaryCorollary.lean:90`
  `sorry` 和 `source_hashes_match: false`，均不在本 lane 修改范围内。
- 提交：本报告所在的 lane commit；未 push、merge 或 rebase。
