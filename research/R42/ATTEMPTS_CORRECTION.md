# R42 item 1e-i — correction datum path (lane 075)

Module: `formalization/NSFormalization/Section4/R42/CorrectionPath.lean`
(two lemmas, no `sorry`/`axiom`/`native_decide`/`maxHeartbeats`).
Axioms: `propext, Classical.choice, Quot.sound` for both public declarations
(`research/R42/axioms_correction.lean`).

## What the two lemmas are

* `exists_datumPath_of_localized` — the unit (item **1e-i** of `LIFESPAN_SPLIT.md`).
  A field `d` that is `ContDiffOn ℝ ∞` on `Ico 0 T × ℝ³`, spatially supported in a
  fixed ball at each `t ∈ Ico 0 T`, and `= 0` for `0 ≤ t ≤ t₁` (`t₁ > 0`), has for
  every `S < T` and every `m : ℕ` an order-`m` datum path continuous on `Ico 0 S`.
* `sobolev_add_of_localized` — additivity assembly: `v` with the `sobolev`-shaped
  hypothesis on `Ico 0 T'` (`T' ≥ S`) plus `d`'s on `Ico 0 S`, both with continuous
  slices on `Ico 0 S`, give `v + d` a datum path continuous on `Ico 0 S`.

## Route (as executed)

Lemma 1: build the global field `F p := if 0 ≤ p.1 then χ p.1 • d p else 0`, with
`χ t := Real.smoothTransition ((b - t)/(b - S))`, `b := (S+T)/2`.  Then
`χ = 1` on `Iic S` (`one_of_one_le`, `le_div_iff₀`), `χ = 0` on `Ici b`
(`zero_of_nonpos`, `div_nonpos_iff`).

* `ContDiff ℝ ∞ F` via `contDiff_iff_contDiffAt` on the open time-cover
  `Iio t₁` (F = 0, using `hhist` + the hard cutoff and `t₁ > 0`), `Ioo 0 T`
  (F = χ • d, `hd.mono` + `(χ∘fst)`-smooth `ContDiffOn.smul`), `Ioi b` (χ = 0);
  each point handled by `ContDiffAt.congr_of_eventuallyEq` off `contDiffAt_const`
  or the `ContDiffOn.smul` datum. The cover is `ℝ` because `t₁ > 0` and `b < T`.
* `HasCompactSupport F` via `HasCompactSupport.intro` with
  `K = Icc 0 b ×ˢ closedBall x₀ r` (`isCompact_Icc.prod isCompact_closedBall`);
  outside `K`, either `p.1 < 0` (hard cutoff), `p.1 > b` (χ = 0), or
  `p.2 ∉ closedBall` ⟹ `d = 0` (`hsupp` + `image_eq_zero_of_notMem_tsupport`).
* `G := I03.angularPath m F`; continuity from `D01.contDiff_angularPath`; the datum
  at `t ∈ Ico 0 S` from `I03.angularPath_pairing` after rewriting `F (t,x) = d (t,x)`
  (there `χ t = 1`, `0 ≤ t`), no `isSobolevDatum_unique` needed.

Lemma 2: `G := G_v + G_d`; continuity `ContinuousOn.add` (+ `.mono` via
`Ico_subset_Ico le_rfl hS`); datum `D01.isSobolevDatum_add`, with the two
`SchwartzPairable` side conditions from `D01.schwartzPairable_of_isSobolevDatum`
(order `(m:ℝ) ≥ 0` from `Nat.cast_nonneg`, slice continuity from `hvc`/`hdc`).

## Type-name findings

* `SpaceTimeField` (A02) and `VelocityField` (the type `I03.angularPath` takes) are
  the *same* abbreviation `ℝ × Space → Space` (`NavierStokes.ProblemStatement`;
  A02 `abbrev SpaceTimeField := VelocityField`). No bridge needed.
* Statements use `A02.IsSobolevDatum` (matching `ClassicalSolutionR.sobolev`);
  `D01.isSobolevDatum_add` / `schwartzPairable_of_isSobolevDatum` are stated with
  `D01.IsSobolevDatum` / `D01.SchwartzPairable`, and apply directly because
  `A02.IsSobolevDatum = D01.IsSobolevDatum` definitionally (both unfold to the same
  `angularRealization … = ∫ …` pairing; verified by lane 040, used silently here).
* `angularPath_pairing` yields exactly the pairing that both `IsSobolevDatum` defs
  unfold to, so the order-`m` datum of `fun x => F (t,x)` is literally
  `fun i ψ => angularPath_pairing … t i ψ`.

## Failed / adjusted approaches

1. **`dsimp only [hFdef]` made no progress.** With `set F := … with hFdef`
   (`hFdef : F = fun p => …`), `dsimp only [hFdef]` refused to rewrite the
   `set`-bound `F`, while `simp only [hFdef]` unfolds + beta-reduces (and reduces
   `(t,x).1 → t` on literal pairs). Switched all three occurrences to `simp only`.
2. **`image_eq_zero_of_notMem_tsupport hnotmem` picked the wrong `f`.** With the
   ascription `have hdz : d p = 0 := …`, expected-type propagation unified
   `f x = d p` as `f := d, x := p`, demanding `hnotmem : p ∉ tsupport d` (wrong).
   Fixed by destructuring `p` to `(pt, px)` and elaborating the lemma with **no**
   misleading ascription (`have hdz0 := image_eq_zero_of_notMem_tsupport hnotmem`
   infers `f := fun x => d (pt,x)` from `hnotmem`), then re-ascribing
   `have hdz : d (pt, px) = 0 := hdz0` (pure defeq, no re-inference). By contrast
   `hhist q.1 h0 … q.2 : d (q.1,q.2) = 0` has a fully-determined type, so
   `have hdq : d q = 0 := hhist …` succeeds by Prod-eta defeq with no destructure.
3. **`split_ifs` consumes a sign hypothesis in context.** In the `Ioo 0 T` branch a
   premature `have hq0 : 0 ≤ q.1` made `split_ifs` collapse to the single true
   branch (leaving `· rfl` / `· exact absurd …` with "no goals"); removed the
   `have` so `split_ifs with h0` yields both branches. In `hFd`, `ht0 : 0 ≤ t` is a
   binder, so `split_ifs` there legitimately collapses to one goal (bare
   `split_ifs` then the `rw`).
4. **`if_pos`/`if_neg` are deprecated** in this toolchain (v4.34.0-rc2 core):
   replaced every `rw [if_pos/if_neg …]` by `split_ifs`.

## Commands

* `cd verification && lake build NSFormalization.Section4.R42.CorrectionPath`
  → `Build completed successfully (9879 jobs).` (no warnings from the new file).
* `cd verification && lake env lean ../research/R42/axioms_correction.lean`
  → both declarations depend on `[propext, Classical.choice, Quot.sound]`.
* `make check` → architecture checks, `test_contract_policy` (13 tests), and
  `check_work_queue` (30 items) all OK.
