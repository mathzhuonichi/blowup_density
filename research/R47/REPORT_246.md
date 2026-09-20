# Lane 246-SPEC-r47-spec report

## 1. 证了哪个定理

完成了 Theorem 4.7 `thm:Rgrid`（`04-whole-space.tex:297-304`）的 reconciled
specification；本 lane 只陈述合同，不证明定理。陈述固定正黏性、原初值与参考力、在
`T+δ` 上的实际经典参考解，以及有限网格族 `Fin n → Grid`，然后存在同一个插入族，
使所有网格的速度/力 cell observations 在每个 `0 ≤ t < T` 相同，同时保留早期历史、
紧支撑力差、精确最大寿命、能量与三项力范数收敛，以及同一个球内的速度/压力/力
支撑。

按 lead reconciliation，公共球只要求普通的 `ball ⊆ cell`，不把 proof 中的
`closure ball ⊆ interior cell` 加强写进 theorem；压力 gauge 在每个 ε 先选一个
`c : ℝ → ℝ`，可随时间变化但在空间上常数。

## 2. Lean 里现在有什么

`research/R47/Spec.lean` 在
`BlowupDensity.Research.R47.Draft` namespace 中给出 reconciliation 明确要求的
`RGridFamily` 和单字段 `RGridAPI.choose`。`RGridFamily` 的字段名、raw-data 参数和量词
顺序均照 binding decision：`center`, `radius`, `radius_pos`, `containingCell`, `ε₀`,
`eps_pos`, `force`, `solution`, `force_mem`, `history`,
`forceDifference_compact`, `velocity_observations`, `force_observations`, `lifespan`,
`energy_convergence`, `force_convergence`, `velocity_support`, `pressure_support`,
`force_support`。每个字段都有 paper line citation 与 non-vacuity 说明；没有本地
placeholder `Prop`。

三项力收敛的第一项采用 lead addendum 指定的 manuscript-literal
`mixedLebesgueENorm 1 2`，另两项是 `forceSobolevENorm 2 (-1)` 与
`forceHomogeneousENorm 2 (-1)`。R47 不重复 Proposition 4.6 在
`04-whole-space.tex:218-220` 的 completed-density conjuncts；它只保留 R47 在 `:303`
明确引用的 `:221-228` energy/force convergence conjuncts。

按要求加入并由 Lean 验证了两个 definitional checks：在
`q : ℝ≥0∞`, `(q = 1 ∨ q = 2)`, `s < criticalOrder q.toReal` 的精确参数形状下，
`CompletedDense` 展开为 `CompletedDenseVia … (IsSobolevPath s)`；以及
`CompletedDenseHomogeneous 2 (-1)` 展开为
`CompletedDenseVia … (IsHomogeneousPath (-1))`。两者均为 `example … := rfl`。

六个 provenance 文件从 lanes 240/241 原样复制；逐个 `git hash-object` 与源 branch
blob 比较全部 `MATCH`。`COMPARISON.md` 给出 paper clause → final field → A/B provenance
→ ruling 表，逐字收录 reconciliation 的 “Proof dependencies”，并列出 owner 问题。

## 3. 缺口是什么

本 lane 没有 theorem inhabitant、binding 或 proof；后续证明依赖 lane 233/R42 的同一
插入族、有限网格共同 cell 的选球 lemma、`gridObservation` locality，以及尚开放的
`L²_tḢ⁻¹_x` convergence（I03），详见 `COMPARISON.md` 的依赖段。

唯一保留给 owner 的 statement/vocabulary 问题是 addendum 中的
`mixedLebesgueENorm 1 2 f = forceSobolevENorm 1 0 f` bridge。实际加入
`example … := rfl` 后 Lean 明确拒绝：两个 definition 的 path carriers 不同
（`Lp Space 2` 与 `RealVectorSobolev 0`），因此它不是 definitional equality；当前也
没有已注册 theorem 可直接证明该等式。最终 spec 按 addendum 使用 literal mixed norm，
owner 可决定是否另注册并证明 order-zero isometry bridge。

## 4. 跑了什么命令、什么结果

- 在 `verification/` 运行
  `. ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/R47/Spec.lean`：
  exit 0，0 errors，0 warnings。
- 同目录分别 elaboration `DraftA.lean`、`DraftB.lean`：均 exit 0。
- 两个 completed-density `example … := rfl` 随 `Spec.lean` 成功 elaboration。
- 临时 mixed/Sobolev equality `example … := rfl`：按预期失败，报 type mismatch；该失败
  probe 已从最终可 elaboration 文件移除，结论记录在 spec comment、comparison 与本报告。
- 六个 provenance 文件以 `git hash-object` 对比各自 source branch blob：全部一致。
- `git diff --check`：通过；`Spec.lean` 的
  `sorry|admit|axiom|native_decide` 扫描：无匹配。
- 从 repository root 运行
  `. scripts/lean-env.sh && LEAN_NUM_THREADS=6 bash scripts/gates.sh`：exit 0；
  `make check`、`make test`、`make test-mutations`、最终 contract check 全部通过，输出
  `gates OK`。
