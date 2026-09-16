# Lane 244 — R45 reconciled specification

## 1. 规范了哪个定理

按 lead 的 `research/R45/RECONCILIATION.md`，完成了
`cor:Rclasses`（`paper/sections/04-whole-space.tex:194-199`）的协调后 Lean
规格。它把 Theorem 4.1 的四项结果准确限制到 `F_c` / `F_rd`：一般
`X_R` 初值的次临界相对稠密性、零初值完整 iff、`F_rd` 中 Schwartz
初值的显式特例，以及正则参考解附近保持早期历史、恰在 `T` 终止并在力
范数与 `E_T` 中同时逼近的附句。本 lane 只给 statement，不证明该推论。

## 2. Lean 里现在有什么

`research/R45/Spec.lean` 在 `BlowupDensity.R45.Draft` 中定义唯一结构
`RClassesAPI`，字段恰为 `density`、`zeroIff`、`schwartzDensity`、
`regularReference`。前三个适用位置及 rider 全按 reconciliation 固定：

- 环境类由 `Y = forceClassCompact ∨ Y = forceClassRapid` 限定；
- `q : ℝ≥0∞`，并要求 `q = 1 ∨ q = 2`；
- 阈值统一为注册的 `criticalOrder q.toReal`；
- rider 只要求 `a ∈ initialClassR`，用任意 `0 ≤ τ < T`，并删去属于 R42
  的末时无界速度 conjunct；
- 每个字段 docstring 都给出论文行号、完整量词顺序和 non-vacuity 说明。

同一文件中的两个 `example ... := rfl` 已核实：`CompletedDense` 和
`CompletedDenseHomogeneous` 分别 definitionally equal 于采用
`IsSobolevPath` 和 `IsHomogeneousPath` 的 `CompletedDenseVia`。它们不进入
`RClassesAPI`，因为 R45 讨论光滑子类的相对拓扑，不是完成空间稠密性。

`research/R45/COMPARISON.md` 合并了 paper-clause → Lean-field 表、A/B
来源、逐项 ruling、精确量词与 conjunct 顺序、non-vacuity 审计，并逐字
保留 reconciliation 的 “Proof dependencies” 段及 owner open questions。

六个 provenance 文件也已加入，且本地 blob 与来源分支逐一相同：

| 文件 | 来源 blob = 本地 blob |
|---|---|
| `DraftA.lean` | `8f1f10a3d7e7e3706337bd92c527cda79b53ab94` |
| `COMPARISON_A.md` | `93a31c52c5df01f65dc6c7589cf60511eaa13a38` |
| `REPORT_238.md` | `2a70377a903f97e8c150df402aa545569f26e684` |
| `DraftB.lean` | `dfd1efd4da6a549d7973c78131f255bf1733e033` |
| `COMPARISON_B.md` | `a9e51f6898eb6078649dee224d64c842ebf1083d` |
| `REPORT_239.md` | `0c08c85cc63c48d88a2b1942213a4760464a54c4` |

本 lane 只新增 `research/R45/` 下九个文件；没有修改现有 Lean 模块、论文、
合同、binding、test 或台账。

## 3. 缺口是什么

R45 的 statement reconciliation 已无数学措辞缺口，但尚未注册为
`verification/Contracts/V1/ForceClasses.lean`，也没有 binding、test 或四个
字段的证明。证明依赖保持 lead 的分解：一般密度/零 iff 依赖 Theorem 4.1
及 G2/G3，Schwartz 特例依赖 G4 + 一般密度，正则参考解附句依赖 lane 233
的记录与 R42 字段。

仅余两个不影响 statement 的 owner bookkeeping 问题：reconciliation
开头把 Draft A 写成七字段，而实际来源及 lane 238 报告为八字段；以及未来
注册/一致性测试是否需要重复本 research spec 中两个 completed-density
`rfl` 检查。详见 `COMPARISON.md` 的 “Open questions for the owner”。

## 4. 跑了什么命令、什么结果

所有 Lean 命令均加载 `scripts/lean-env.sh`，Lake 从 `verification/` 运行，
并使用 `LEAN_NUM_THREADS=6`。

- `lake env lean ../research/R45/Spec.lean`：exit 0，零输出、零错误；两个
  `rfl` 检查同时通过。
- `lake env lean ../research/R45/DraftA.lean` 与
  `lake env lean ../research/R45/DraftB.lean`：均 exit 0，零输出。
- 六次来源 `git rev-parse <branch>:<path>` 与本地 `git hash-object <path>`：
  六组 hash 全部相同，确认 verbatim provenance。
- `LEAN_NUM_THREADS=6 scripts/gates.sh`：exit 0；`make check`、`make test`、
  `make test-mutations`、`check_contracts` 全部通过，13 项合同策略测试通过，
  30 个 work item 一致，mutation suite 按要求拒绝额外公理和削弱假设。
- `git diff --cached --check`：exit 0；`Spec.lean` 中无
  `sorry` / `admit` / `axiom` / `native_decide`。

未 push、merge 或 rebase；交付提交留在 `erenup/244-SPEC-r45-spec`。
