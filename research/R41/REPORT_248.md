# Lane 248 report

## 1. 规范了哪个定理

`Spec.lean` 给出论文 Theorem 4.1（`thm:Rmain`）的 reconciled statement：固定初值的次临界相对稠密性、零初值的精确 `↔`、两个阈值数值，以及围绕每个 regular reference 的同一插入族 rider。陈述严格采用 lead 决定的 `q : ℝ≥0∞`、`q = 1 ∨ q = 2` 和 `criticalOrder q.toReal`，保留精确 lifespan、较早历史、力收敛与 `E_T` 收敛，删除非论文条件 `2*ε₀^2<T`，也不重复 R42 的独立 blow-up-limsup、支集和定量速率子句。

## 2. Lean 里现在有什么

新增 `BlowupDensity.R41.Draft.RMainAPI`，只有四个具名命题字段：`fixedInitialDensity`、`zeroInitialDensityIff`、`thresholdValues`、`regularReferenceApproximation`。每个字段的 docstring 都标出 `04-whole-space.tex` 行号、完整量词顺序和 non-vacuity；rider 内联一个共享的 `(f,u)` family，没有新增辅助 structure 或占位 `Prop`。`Spec.lean` 还用两个 `example … := rfl` 验证：`CompletedDense` 与 `CompletedDenseVia … (IsSobolevPath s)` 定义相等，`CompletedDenseHomogeneous` 与 `CompletedDenseVia … (IsHomogeneousPath s)` 定义相等。

两条 blind lane 的六个 provenance 文件已逐 blob 复制；源分支 blob id 与本地 `git hash-object` 逐项相同。`COMPARISON.md` 合并了 paper-clause 对照、A/B 来源和 reconciliation rulings，并逐字段记录 lanes 232/233/235 的 binding plan，特别写明 232 的 real `q` 到本规范 ENNReal `q` 的 `1/2` 分情况适配，以及 232 的 only-if 与 235 的 if 合成一个 `↔`。

## 3. 还缺什么

规范层没有开放问题。后续 lane 249 仍需注册正式 V1 contract 并完成 bindings/tests：`fixedInitialDensity` 与 `↔` 的 if 方向直接接 lane 235；only-if 方向对 `q=1,2` 分情况接 lane 232；regular-reference rider 从 lane 233 的 R42 V2 family 提取同一组 witnesses，并由 `energyRate` 推出定性的 `energyENorm` 极限。这些是已落地结论之间的适配，不需要新的分析或 owner 的 statement 决策。

## 4. 跑过的命令和结果

- `cd verification && lake env lean ../research/R41/Spec.lean`：exit 0，0 errors，两个 `rfl` checks 均通过。
- `cd verification && lake env lean ../research/R41/DraftA.lean`：exit 0，0 errors。
- `cd verification && lake env lean ../research/R41/DraftB.lean`：exit 0，0 errors。
- `git rev-parse <source-branch>:<path>` 与 `git hash-object <copied-path>`：六组 object id 全部逐项相同，确认 provenance verbatim。
- `git diff --check`：通过。
- `make check`：exit 0，architecture / contract-policy / work-queue checks 全部通过。
- `make test`：exit 0；全部已注册 contract tests 通过（仅有既存依赖的 linter warnings）。
- `make test-mutations`：exit 0；mutation suite 通过，三种非法变异均按预期被拒绝。
