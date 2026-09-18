# 317-T11 / U9c — ConvolutionBound

## 1. 证明的定理（精确陈述）

```lean
theorem torusConvolutionInput : TorusConvolutionInput
```

这里的目标保持 lane 313 原文，无额外假设：

```lean
def TorusConvolutionInput : Prop :=
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k
```

构造与推论：

```lean
def torusConvolutionCLM :
    PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2

theorem torusConvolutionCLM_coeff (A B : PeriodicSobolev 3)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM A B).1 i k = torusProjectedConvectionSymbol A B i k

theorem torusConvolutionCLM_norm_le :
    ‖torusConvolutionCLM‖ ≤ torusConvolutionConstant

theorem torusTwoSpaceContract_nonempty' (ν : ℝ) (hν : 0 < ν) :
    Nonempty (TorusTwoSpaceContract ν)
```

`torusConvolutionConstant = 9 * sqrt (64 * ∑' k, (W(k)^3)⁻¹)`。
核心为卷积核平方界、格点逆三次权可求和、ℓ² Cauchy–Schwarz、
双重求和换元。先证明完整标量序列属于 ℓ²，后封装实向量数据，
复用 T10 Leray 收缩，最终用 `LinearMap.mkContinuous₂` 构造映射。
不需要有限支撑、无散输入或新的分析假设。

## 2. 文件与 Lean 产物

- `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean`：完整证明、
  数据/双线性映射构造、明确常数、目标及推论、非零常数模式的非空例。
- `research/T11/probes/convolution_bound_closes.lean`：逐字展开存在目标，
  检查命名目标、系数身份、算子界、任意正黏性合同和黏性 1 的实例。
- `research/T11/axioms_convolution_bound.lean`：42 个命名声明（含 22 个私有辅助声明）逐项 `#guard_msgs (whitespace := lax)`，公理列表精确为
  `[propext, Classical.choice, Quot.sound]`。私有声明通过内置 `#print axioms` 命令按内部名字审计。
- `research/T11/ATTEMPTS_CONVOLUTION_BOUND.md`：搜索范围、证明路线、真实报错及修复。
- `research/T11/T11_SPLIT.md` §1：仅追加 U9c 状态行。

所有已有 Lean 模块保持不变。无 push、merge 或 rebase。按照本 lane 的
“新文件”限制，不修改 `NEXT_SESSION.md` 或全局 lessons；交接由本报告承担。

## 3. 缺口与报错

本目标无缺口，无 residual named input。`torusConvolutionInput` 不依赖
`PeriodicQuantitativeLocalInput'`。本 lane 完成 H³×H³→H² 系数分析；
后续物理恢复、共同时间窗全阶 bootstrap 仍属于 U9d。

调试曾出现 `HPow ℂ ℝ` 类型推断错误、`Summable.comp_injective` 的
400000-heartbeat 超时、缺少显式 Leray import、以及公理输出换行不匹配；
均已修复，原始错误文本及对应解法见 attempts。最终新模块无警告或错误。
唯一提高 heartbeat 的声明是向量范数界，局部 400000，附注释。

## 4. 命令与结果

所有 Lean 命令先 `. scripts/lean-env.sh`，从 `verification/` 执行，
`LEAN_NUM_THREADS=6`。

| 命令 | 结果 |
|---|---|
| `lake build NSFormalization.Section3.T11.ConvolutionBound` | exit 0；新模块编译成功 |
| `lake env lean ../formalization/NSFormalization/Section3/T11/ConvolutionBound.lean` | exit 0；无错误/警告 |
| `lake env lean ../research/T11/probes/convolution_bound_closes.lean` | exit 0；目标及非空探针通过 |
| `lake env lean ../research/T11/axioms_convolution_bound.lean` | exit 0；42 个精确公理断言通过 |
| 根目录 `make check` | exit 0；合同政策 13 项测试通过，45 工作项一致 |
| 根目录 `LEAN_NUM_THREADS=6 make test` | exit 0；已注册合同闭包通过 |
| 根目录 `LEAN_NUM_THREADS=6 make test-mutations` | exit 0；3 个不合法变异被拒绝，合法重构被接受 |
| `git diff --check` | exit 0 |

完整输出保留在本 worktree 的忽略目录 `tmp/317-*.log`。
