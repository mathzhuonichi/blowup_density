# REPORT 337 — T11 U14 `extendsBeyond` + U16 `lifespanInfiniteOfLocallyFinite`

Branch `erenup/337-T11-U14-U16-extends-lifespan`, base = integration + lanes
332 (`RestartBeyond.lean`) and 322 (`HighOrder.lean`).

## 1. 证了哪个定理

第 3 节附录 A 的连续化两步，即 `PeriodicContinuationAPI` 的最后两个字段，
逐字取自 `research/T11/probes/api_on_canonical.lean:136-158`：

- **U14 `extendsBeyond`**：设 `0 < ν`、`a ∈ initialClassT`、`f ∈ forceClassT`、
  `0 < S`，若 `(u, p)` 在 `S` 以下每个正视界上都是经典解（`SolvesBelowT`）且满足
  连续化判据 `squaredHTwoIntegralT S u ≠ ⊤`（`∫_{(0,S)} ‖u(t)‖²_{H²} dt < ∞`），
  则 `ExtendsBeyondT ν a f S u p`：存在 `δ > 0` 和**具体的**
  `ClassicalSolutionT ν a f (S + δ)`，其速度与压力在 `[0, S)` 上逐点等于
  `(u, p)`。这比已注册的 `A04.extendsBeyond`（结论只有
  `ofReal S < maximalLifespanR`）严格更强。
- **U16 `lifespanInfiniteOfLocallyFinite`**：若 `(u, p)` 是极大解，且对每个
  `S > 0` 满足 `ENNReal.ofReal S ≤ maximalLifespanT ν a f` 时判据都有限，则
  `maximalLifespanT ν a f = ⊤`。论文 `03-torus.tex:500-502` 就在这一步。

两条都只依赖两件事，别无其他：单一命名输入 `PeriodicQuantitativeLocalInput'`
（通过 332 的 `restartBeyond` 消费），以及作为**显式 binder** 的 `hHigh`
（= `higherOrderBound` 字段原文，因为 U12 还在 335/336 手里）。`hHigh` 不是新的
`def … : Prop`；探针第 3 个 example 用 322 的
`higherOrderBound_of_energyInequality` 把它接上，证明它确实与 U12 的结论
token 相同。

路线与计划一致：`hHigh` 取 `m = 1` 给出 `[0, S)` 上**一致**的 `H¹` 界
`K ≠ ⊤`（字段本身把 `∃ M` 放在 `∀ t` 之外，常数就是端点常数，不随 `b ↑ S` 退化），
这正是 332 `restartBeyond` 的前提，其 `δ` 在数据之前选定；U16 反证：若
`L := maximalLifespanT ≠ ⊤`，取 `S = L.toReal`（`≤` 在这里是承重的），极大解在
`L` 以下每个视界上给出 `SolvesBelowT`，U14 给出 `S + δ` 上的解，于是
`ofReal (S + δ) ≤ L = ofReal S`，即 `δ ≤ 0`，矛盾。

## 2. Lean 里现在有什么

新模块 `formalization/NSFormalization/Section3/T11/ExtendsBeyond.lean`，9 个声明：

| 声明 | 内容 |
|---|---|
| `lifespan_ge_of_horizon` | 已实现的视界是 `maximalLifespanT` 上确界的一项（`horizon_le_lifespan` 的逐点形式） |
| `lifespan_ge_of_extends` | **导出**：`ExtendsBeyondT` ⟹ `∃ δ > 0, ofReal (S + δ) ≤ maximalLifespanT` |
| `extendsBeyond_of_input` | **U14 目标，逐字** |
| `periodicMaximalExistenceInput_of_input` | 桥：`PeriodicQuantitativeLocalInput'` ⟹ 323 的 `PeriodicMaximalExistenceInput` |
| `exists_maximal_of_input` | `PeriodicLocalTheoryAPI.exists_maximal` 逐字，现在也只依赖那一个名字 |
| `lifespanInfiniteOfLocallyFinite_of_input` | **U16 目标，逐字** |
| `squaredHTwoIntegralT_ne_top_of_lt` | 判据在视界内部自动成立：`S < T` ⟹ `squaredHTwoIntegralT S w.velocity ≠ ⊤` |
| `constantVelocitySolutionT` | 非空性见证：常值无散度速度 + 零力 + 零压，在**每个**正视界上的经典解 |
| `squaredHTwoIntegralT_constant_ne_top` | 常值速度的判据在每个视界上有限 |

外加模块内一个无条件的非空性 `example`：`a ∈ initialClassT`、
`0 ∈ forceClassT`、`u (0,0) ≠ 0`、`SolvesBelowT`、判据有限、
`IsMaximalPeriodicSolution`、局部有限判据，七项同时被非零解满足。

9 个声明全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`
（`research/T11/axioms_extends_beyond.lean`，`#guard_msgs` 逐条钉住）。
无 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。

探针 `research/T11/probes/extends_beyond_closes.lean` 7 个 example：两个目标逐字、
`hHigh` 与 322 结论对接、`lifespan_ge_of_extends` 导出、`exists_maximal` 导出、
`≤` 承重性的机器检验、两个非空性（假设侧无条件 + 结论侧条件于 `H`/`hHigh`）。

## 3. 缺口是什么

1. **`PeriodicQuantitativeLocalInput'` 未证**（U9/U11 的题）。这是整个 T11 唯一的
   命名输入，321/332/337 共用它；337 额外把 323 的
   `PeriodicMaximalExistenceInput` 也归约到它，所以第 3 节连续化链现在只剩这一个名字。
2. **`hHigh` 未证**：322 已把它归约到手稿的 `eq:Rhigh`（`hRhigh` + 常数族
   `Chigh`），`hRhigh` 由 335/336 在做。U17 装配时若 335/336 落地，直接把
   `higherOrderBound_of_energyInequality Chigh hRhigh` 代进来即可（探针已验证）。
3. `horizon_le_lifespan`（315）在 U16 里**用不上**：它要的是全局
   `horizon`/`solution` 族，而连续化只有单个数据上的单个解。这不是缺口，是
   `lifespan_ge_of_horizon` 存在的理由，细节写在
   `ATTEMPTS_EXTENDS_BEYOND.md` §1。U17 装配时仍应用 315 的版本。
4. 非空性用的是常值解 + 零力，不是 `nonzero_forced_witness'`：后者的力只知道光滑、
   周期、`L¹_t H^m` 有界，**不在** `forceClassT` 里（缺时间紧支撑），而两个目标都对
   `f ∈ forceClassT` 量化。见 `ATTEMPTS_EXTENDS_BEYOND.md` §4。

## 4. 跑了什么命令、什么结果

```
LEAN_SEED_DIR=… bash scripts/lean-install.sh                        → == OK
cd verification && LEAN_NUM_THREADS=6 lake build \
  NSFormalization.Section3.T11.ExtendsBeyond                        → Built, 0 errors (10566 jobs)
lake env lean ../formalization/NSFormalization/Section3/T11/ExtendsBeyond.lean
                                                                    → 0 errors, 0 warnings
lake env lean ../research/T11/probes/extends_beyond_closes.lean     → 0 errors, 0 warnings
lake env lean ../research/T11/axioms_extends_beyond.lean            → 0 errors (9 × #guard_msgs pass)
make check (worktree root)                                          → OK
```
