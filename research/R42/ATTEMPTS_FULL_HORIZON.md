# R42 full horizon — attempts (lane 098)

Module: `formalization/NSFormalization/Section4/R42/FullHorizon.lean`.
Goal: upgrade lane 087's per-`S` shorter-horizon solutions to a single classical
solution on the full horizon `[0,T)`, by gluing the datum paths through datum
uniqueness. One bounded unit: Lemma A (gluing) + Lemma B (horizon-`T` solution).
Lemma C (`IsMaximalSolution`) is `MAXIMAL_SPLIT.md`, table only.

## What was proved

* `exists_datumPath_of_forall_shorter` (Lemma A): from a datum path on `Ico 0 S`
  for every `0 < S < T`, produce one on `Ico 0 T`.
* `classicalSolutionR_of_inserted_fullHorizon` (Lemma B): the horizon-`T`
  classical solution, with exactly lane 087's hypotheses plus `0 < T`.

Both rest only on `{propext, Classical.choice, Quot.sound}`
(`axioms_full_horizon.lean`).

## Route that worked (first compile, one deprecation fix)

### Lemma A — per-point choice + uniqueness

* `choose Gs hGsc hGsd using h` turns the per-`S` existence into a function
  `Gs : (S) → 0 < S → S < T → (ℝ → RealVectorSobolev m)` with its continuity and
  datum properties.
* Glue: `G t := if 0 ≤ t ∧ t < T then Gs ((t+T)/2) _ _ t else 0`. The horizon
  `b t = (t+T)/2` satisfies `0 < b t` (from `0 ≤ t`, `0 < T`), `b t < T` and
  `t < b t` (from `t < T`); these three `linarith` facts are hoisted as `hb0`,
  `hbT`, `hbt` and reused at both the running `t` and the base point `t₀`.
* Datum at `t ∈ Ico 0 T`: `G t = Gs (b t) _ _ t`, and `t ∈ Ico 0 (b t)` since
  `t < b t`, so `hGsd` gives the datum directly.
* Continuity at `t₀ ∈ Ico 0 T`: the single path `Gt₀ := Gs (b t₀) _ _` is
  `ContinuousOn (Ico 0 (b t₀))`, hence `ContinuousWithinAt … (Ico 0 (b t₀)) t₀`.
  `Ico 0 (b t₀) ∈ 𝓝[Ico 0 T] t₀` via `mem_nhdsWithin` with the open witness
  `Iio (b t₀)` (`t₀ < b t₀`; `Iio (b t₀) ∩ Ico 0 T ⊆ Ico 0 (b t₀)`), so
  `ContinuousWithinAt.mono_of_mem_nhdsWithin` lifts it to
  `ContinuousWithinAt Gt₀ (Ico 0 T) t₀`.
  `G =ᶠ[𝓝[Ico 0 T] t₀] Gt₀`: on `Ico 0 (b t₀)`, `G t = Gs (b t) _ _ t` and
  `Gt₀ t = Gs (b t₀) _ _ t` are both data of the **same** slice `u(t,·)`, so equal
  by `D01.isSobolevDatum_unique`. Transfer with
  `ContinuousWithinAt.congr_of_eventuallyEq_of_mem`.

Two design choices that avoided friction:

1. **`congr_of_eventuallyEq_of_mem` (not `congr_of_eventuallyEq`).** The `_of_mem`
   variant needs only `t₀ ∈ Ico 0 T`, sidestepping a separate proof of the
   pointwise equality `G t₀ = Gt₀ t₀` at the base point.
2. **`D01.isSobolevDatum_unique` applies to `A02.IsSobolevDatum` data by defeq.**
   `ClassicalSolutionR.sobolev` carries A02-flavoured data; the D01 uniqueness
   lemma unifies through the recorded `A02.IsSobolevDatum = D01.IsSobolevDatum`
   defeq, so no bridge/transport was needed. (Same defeq lane 087 already uses for
   `isSobolevDatum_add`.)

### Lemma B — the horizon-`T` solution

* All fields except `sobolev` and `pressure_gradient` are the hypotheses verbatim
  (already on `Ico 0 T` / `Ioo 0 T`); `horizon_pos := hT`.
* `sobolev`: for each `m`, feed `exists_datumPath_of_forall_shorter` the family
  `S ↦ (classicalSolutionR_of_inserted … S).choose.sobolev m`, rewriting
  `w.velocity = u` (`rwa [hv]`) so the datum is of `u(t,·)`.
* `pressure_gradient`: `memLp_pressureGradient_of_difference_support` (lane 083) at
  horizon `T` directly — its statement is at a single horizon, so no restriction of
  the target interval is needed; only the reference pressure smoothness is restricted
  from `Ico 0 (T+δ)` to `Ico 0 T` with `.mono (Set.prod_mono …)`, exactly as lane
  087 does for the shorter horizon.

`0 < T` is a genuine extra hypothesis (lane 087 got `0 < S` from `hS0`; there is no
`0 < T` in the shared hypotheses — `ref.horizon_pos` only gives `0 < T + δ`). It is
`CorrectionAPI.time_pos` at the Bindings level.

## Failed / rejected approaches

* **No compile failures.** The module type-checked on the first `lake build`; the
  only edit afterwards was cosmetic.
* **`dif_pos` → `dite_eq_left`.** `rw [dif_pos htc]` compiled but emitted a
  deprecation warning (`dif_pos` is `@[deprecated dite_eq_left]` in
  `Init/Core.lean:1209` of v4.34.0-rc2). `dite_eq_left hc` has the identical
  signature `dite c t e = t hc`, so both occurrences were switched; module is now
  warning-free.
* **Not attempted: proving `IsMaximalSolution` in Lean this lane.** Per task,
  Lemma C is table-only (`MAXIMAL_SPLIT.md`). The table records that it is a ~5-line
  consequence of lane 087 + `lifespan_eq` and does **not** need Lemma B.
* **Considered but unnecessary: a single global datum path independent of `t`.**
  One might try to pick one `S`-path and extend; but no single `S < T` covers
  `[0,T)`. The per-point midpoint `(t+T)/2` is the minimal device that both covers
  every `t < T` and keeps a fixed path valid on a whole neighbourhood of each `t₀`.

## Commands

* `cd verification && lake build NSFormalization.Section4.R42.FullHorizon` →
  `Build completed successfully (9884 jobs)`, `Built … (4.4s)`.
* `cd verification && lake env lean ../formalization/NSFormalization/Section4/R42/FullHorizon.lean`
  → silent, exit 0.
* `cd verification && lake env lean ../research/R42/axioms_full_horizon.lean` →
  both declarations `depends on axioms: [propext, Classical.choice, Quot.sound]`.
* `make check` (worktree root) → exit 0.
