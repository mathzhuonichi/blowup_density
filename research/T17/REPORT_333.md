# 333-SPEC-t17-spec

## 1. 证了哪个定理

本 lane 产出了 `lem:correction`（`paper/sections/03-torus.tex:218-285`）的调和规格：注册的 `alpha`、T16 的 `CutoffData`/`LocalPotentialAPI`、T13 的 `LocalizationAPI`、T15 的 `PlacementData`，以及固定圆柱上的 `W_ε` 和括号力 profile。规格保留 `eq:H`、两组导数界、`eq:wE`、`eq:Hmixed`、`eq:HHs`、支持测度/时间长度和 profile rescaling identities。

## 2. Lean 里现在有什么

`research/T17/Spec.lean` 是 Type-valued `BlowupDensity.T17.Spec.CorrectionAPI`。`place : PlacementData P` 固定共享的 `T,x₀,K_*,B,ε₀`；`potential` 与 `localization` 是字段；常数是 ε 量化之前的数据，所有速率界采用实数常数包在单个 `ENNReal.ofReal` 中。`H^s` 项有 `MemForceSobolevT 1 s` guard，能量项有速度和全梯度 `MemLp` guards，力混合范数有逐切片 `MemLp` guard。A/B 草稿、比较表和两份原始报告已逐字保存在同目录。

文件还包含三个漂移检查：注册 `CompletedDense`/`CompletedDenseHomogeneous` 与 `CompletedDenseVia` 的 `rfl` 检查、`alpha` 指数算术 `example`，以及 T15 复制的 mixed-norm/`alphaT` 定义相对注册 `alpha` 的 `rfl` 检查。A 的 `force_exponent_identity` 没有进入结构体。

## 3. 还缺什么

本 lane 只写 specification，不提供证明。仍需证明 T16 cutoff 公式到 `W_ε` 的图表恒等式、力 profile 的仿射链式法则、统一导数常数、周期 lift 的支持测度和时间长度、能量/混合范数的缩放（含两个 `∞` 端点），以及 T13 localization 和端点估计拼接出的 `H^s` 路径。`research/T17/COMPARISON.md` 的 “Proof dependencies” 保留了 reconciliation 的完整八项清单；owner 仍需决定 PlacementData 参数和 mixed norm 是否最终注册到 T10。

## 4. 跑了什么命令、什么结果

- `diff -q research/T17/{DraftA.lean,COMPARISON_A.md,REPORT_294.md}` 与 lane 294 对应 branch 的 `git show`：通过。
- `diff -q research/T17/{DraftB.lean,COMPARISON_B.md,REPORT_295.md}` 与 lane 295 对应 branch 的 `git show`：通过。
- `cd verification && lake env lean ../research/T17/Spec.lean`：0 errors；profile/`alpha`/`CompletedDenseVia` 的 drift examples 均通过。
