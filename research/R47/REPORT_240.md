# Lane 240-SPEC-r47-draft-a report

## 1. 证了哪个定理

完成了 Theorem 4.7 `thm:Rgrid`（identical whole-space cell observations）的
Draft A **陈述**，没有写证明。陈述固定任意有限个完整均匀笛卡尔网格，并把同一个
Theorem 4.2 插入族选到所有网格的共同小球内，使速度和力在每个 cell 上的平均值于
全部 `0 ≤ t < T` 完全一致，同时保留精确爆破时刻及 Proposition `prop:Renergy` 的
能量、力收敛。

## 2. Lean 里现在有什么

`research/R47/DraftA.lean` 中有可 elaboration 的 `RGridAPI`。它复用
`InsertionFamilyAPI`、`Data.Grid`、`Data.gridObservation`、
`Data.maximalLifespanR` 及三个已注册范数；每条论文结论都有显式字段。有限网格族用
`[Finite ι]` 与 `ι → Data.Grid` 表示，因此不需要对实数参数网格提供可判定相等。

文件另有两个具体的本地定义，并明确标记 **needs registration**：
`IdenticalCellObservationsBefore` 精确展开所有 cell、所有 presingular time 的观测相等；
`PressureDifferenceSupportedInBallModuloGauge` 精确展开去掉空间常数 `c(t)` 后的压力
支撑。`research/R47/COMPARISON_A.md` 记录了逐 clause 对照、量词次序与选择理由。

## 3. 缺口是什么

本 lane 只交付双盲 specification，没有 binding 或 proof。两个本地 predicate 在进入
稳定合同前需要注册或以内联形式取代。最终 reconciliation 还应核定 API packaging：
Draft A 把 `RGridAPI` 作为“网格先固定、随后选择一个插入族”的结论 record；从任意
raw regular-reference hypotheses 构造该 record 的全称定理留给绑定层。还需审定压力
gauge 是否公开为时间相关的空间常数，以及是否希望把论文只要求的 `ball ⊆ cell`
加强成证明中使用的 closure containment。Draft A 没有声称 point observations 相等，
也没有声称任意 refinement 下的一致性。

## 4. 跑了什么命令、什么结果

- `. ../scripts/lean-env.sh` 后运行
  `LEAN_NUM_THREADS=6 lake env lean ../research/R47/DraftA.lean`（工作目录
  `verification/`）：成功，exit code 0，无 warning/error。
- `git diff --check`：成功，无 whitespace error。
- `rg -n '\b(sorry|admit|axiom)\b'` 扫描三个交付文件：无匹配（`rg` exit code 1
  表示没有匹配项）。
- `bash scripts/gates.sh`：成功，`make check`、`make test`、
  `make test-mutations` 与最终 contract check 全部完成，输出 `gates OK`。
