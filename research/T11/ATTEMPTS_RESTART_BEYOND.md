# ATTEMPTS — T11/U13 `restartBeyond` (lane 332)

Lane 332 took over from a codex run that died mid-file (capacity), leaving an uncommitted
375-line `Section3/T11/RestartBeyond.lean` in the worktree. A copy of that partial is *not*
kept in the repository; what follows records exactly what was reused and what was replaced.

## 0. What of the previous partial was kept

Kept (mathematically correct, compiled as written):

- `shiftedSolutionT` — **all fields except `momentum`**: the `+b` reindexing of
  `velocity_smooth` / `pressure_smooth` / `divergence` / `sobolev` / `pressure_gradient` /
  `velocity_periodic` / `pressure_periodic` / `pressure_gauge`, and `initial` by
  `simp [timeShiftT, timeShift]`. The design decision behind it was kept too: the torus
  version needs **no** basepoint pressure normalization (unlike the `R³` model
  `Section4.A04.exists_shifted_glue`, which pastes `w.normalizePressure 0`), because
  `ClassicalSolutionT` carries `pressure_gauge : PressureGaugeT (Ico 0 T) p` as a field and
  both charts are therefore already Haar-normalized.
- `shifted_velocity_uniqueT` / `shifted_pressure_uniqueT` — the hypothesis-free restatements of
  lane 315's `velocity_unique` / `pressure_unique`. This is load-bearing and was the previous
  worker's main correct insight: lane 315's versions take `a ∈ initialClassT` and
  `f ∈ forceClassT`, and **`timeShiftT b f ∉ forceClassT` in general** (the compact time support
  `K ⊆ Ioi 0` is translated left by `b` and can reach `t ≤ 0`), so the shifted problem cannot use
  them. Both hypotheses are unused in the Paper 1 route (`toFlow` + `flow_velocity_agree_on_common_interval`
  / `normalized_flows_agree`), so restating without them is sound.
- The whole body of the gluing constructor: the seam at `c = (b+T)/2` strictly inside the overlap,
  the two `overlapPaste` definitions, `hul`/`hur`/`hpl`/`hpr`, and the fieldwise assembly of the
  glued `ClassicalSolutionT` — including the three fields the `R³` model does not have
  (`sobolev` via `datum_unique` + a pasted datum path, `velocity_periodic`/`pressure_periodic` by
  `calc` through the chart, `pressure_gauge` by `unfold pressureMeanT; rw [chart agreement]`).

Replaced or added:

- `shiftedSolutionT.momentum` and `restartedResidualT` — both were broken (see §1).
- The duplicated overlap calculus (`overlapPasteT`, `overlapPasteT_left/right`,
  `contDiffOn_overlapT`, `continuousOn_overlapT`, ~50 lines) was **deleted**: the `Section4.A04`
  originals are type-generic (`{E : Type*}`, `SpaceTime`, `Space`) and apply verbatim. The module
  now `open`s them.
- `glueClassicalSolutionT`'s conclusion was strengthened from `Nonempty (ClassicalSolutionT ν a f (b+L))`
  to `∃ v, (velocity agrees with w on Ico 0 T) ∧ (pressure agrees with w on Ico 0 T)`. `Nonempty`
  loses exactly the information U13/U14/U16 need.
- New: `velocity_hasDerivAt_timeT`, `velocitySlice_mem_initialClassT`, `restrictClassicalSolutionT`
  (+ two `rfl` projection lemmas), `solvesBelowT_of_classicalSolutionT`, `restartBeyond`, and the
  non-vacuity `example`.

## 1. The two failures in the partial, with exact error text

Both failures were in the time-translation chain rule. The partial tried to build the temporal
derivative by hand out of `DifferentiableAt` + `HasFDerivAt.comp` on `fun s => (s ± b, x)` instead
of reusing the one-dimensional slice derivative:

```
have hd : DifferentiableAt ℝ w.velocity (t + b, x) := …
have hpath : HasFDerivAt (fun s : ℝ => (s + b, x)) ((ContinuousLinearMap.id ℝ ℝ).prod 0) t := …
have hs := hd.hasFDerivAt.comp t hpath
```

`hs.fderiv` then computes the derivative of the *space-time* map, so `congrArg (· 1)` lands on
`fderiv ℝ w.velocity (t+b,x) (1,0)` and not on the time-slice derivative:

```
error: RestartBeyond.lean:117:6: Type mismatch: After simplification, term
  congrArg (fun D => D 1) (HasFDerivAt.fderiv hs)
 has type
  deriv (fun x_1 => w.velocity (x_1 + b, x)) t = (fderiv ℝ w.velocity (t + b, x)) (1, 0)
but is expected to have type
  deriv (fun s => Section4.A04.timeShift b w.velocity (s, x)) t = deriv (fun s => w.velocity (s, x)) (t + b)

error: RestartBeyond.lean:158:4: Type mismatch: After simplification, term
  congrArg (fun D => D 1) (HasFDerivAt.fderiv hs)
 has type
  deriv (fun x_1 => w.velocity (x_1 - b, x)) t = (fderiv ℝ w.velocity (t - b, x)) (1, 0)
but is expected to have type
  deriv (fun s => w.velocity (s - b, x)) t = deriv (fun s => w.velocity (s, x)) (t - b)
```

The second, independent failure: the closing `simpa only [...]` sets dropped `advection` (the `R³`
model has it), so the two sides of the residual never met:

```
error: RestartBeyond.lean:121:4: Type mismatch: After simplification, term
  w.momentum (t + b) ht' x
 has type
  navierStokesResidual ν w.velocity w.pressure (t + b) x = f (t + b, x)
but is expected to have type
  temporalDerivative w.velocity (t + b) x + advection (Section4.A04.timeShift b w.velocity) t x -
      ν • spatialLaplacian (Section4.A04.timeShift b w.velocity) t x +
    pressureGradient (fun z => w.pressure (z.1 + b, z.2)) t x = Section4.A04.timeShift b f (t, x)

error: RestartBeyond.lean:162:2: Type mismatch: … advection w.velocity (t - b) x …
but is expected to have type … advection (fun z => w.velocity (z.1 - b, z.2)) t x …
```

**Fix.** Port `Section4.C01.velocity_hasDerivAt_time` to the torus (`velocity_hasDerivAt_timeT`,
proved from `velocity_smooth` alone) and then follow the `R³` proof literally:
`hd.scomp t ((hasDerivAt_id t).add_const b)` (resp. `.sub_const b`), and close with the `R³` simp
set `[navierStokesResidual, advection, spatialLaplacian, spatialDerivative, pressureGradient,
timeShiftT, timeShift]` (+ `sub_add_cancel` in the `−b` direction). Everything except
`temporalDerivative` is `rfl` under this unfolding, because `spatialDerivative u t y` beta-reduces
to `fderiv ℝ (fun y => u (t,y)) y` and time-translation of `u` only moves the first coordinate.
Both declarations then compile with no `set_option maxHeartbeats`.

## 2. Route decisions taken in this lane

1. **The horizon is reached by choosing the basepoint, not by restricting.** `restart` (lane 321)
   returns one `d > 0` valid for every `t₀ ∈ Icc 0 S`. Taking `t₀ := max 0 (S - d/2)` gives
   `0 ≤ t₀ < S < t₀ + d` for *every* `d > 0` and `S > 0` (the `max 0` covers `d > 2S`, where
   `S - d/2 < 0`), so `δ := t₀ + d - S > 0` and `S + δ = t₀ + d` by `ring`. No case split on
   `d ≤ 2S` and no horizon restriction are needed on the main path.
2. **`SolvesBelowT` is consumed at two different horizons.** Its definition gives, for each
   `b ∈ (0, S)`, a `ClassicalSolutionT ν a f b` whose `velocity`/`pressure` are *literally* `u`/`p`
   (function equality, not just agreement on the slab). The glue uses one such chart at
   `b = (t₀+S)/2`; the final agreement on `[0, S)` uses a *second* chart at `c = (t+S)/2` for each
   `t ∈ [0, S)` and closes by lane 315's `velocity_unique` / `pressure_unique` between the glued
   solution and that chart.
   This is what makes the agreement hold on all of `[0, S)` and not only on `[0, (t₀+S)/2)` — a
   direct read-off of the glue's `hul`/`hpl` would only give the shorter interval. Dead end avoided:
   trying to make `glueClassicalSolutionT`'s chart `T` equal to `S` is impossible, since
   `SolvesBelowT` never supplies a solution *at* `S`.
3. **Pressure agreement is exact, with no additive gauge function** ("needs a lemma" ⑩): both
   charts satisfy `PressureGaugeT`, so `shifted_pressure_uniqueT` (i.e. Paper 1's
   `normalized_flows_agree`, reached through `toFlow` and `integral_torusLift`) gives equality of
   the pressures themselves, not of their gradients. `Section4.A04`'s `normalizePressure_gauge_invariant`
   detour is therefore not needed on the torus.
4. `restrictClassicalSolutionT` was added only because the non-vacuity witness needs a first chart
   strictly shorter than the restart reach (`T' = 1/2 < 1/4 + 3/4`). It is exported anyway:
   `solvesBelowT_of_classicalSolutionT` is its one-line consequence and is the natural supplier of
   `SolvesBelowT` for U14/U16.

## 3. Residual named input

Exactly one, unchanged from lane 321: `PeriodicQuantitativeLocalInput'`
(`Section3/T11/LocalExistence.lean:24`), consumed only through `restart`
(`Section3/T11/Restart.lean`). `RestartBeyond.lean` introduces **no** `def … : Prop`.

## 4. Commands

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.RestartBeyond   # 0 errors, 0 warnings
cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/RestartBeyond.lean   # silent
cd verification && lake env lean ../research/T11/probes/restart_beyond_closes.lean                  # silent
cd verification && lake env lean ../research/T11/axioms_restart_beyond.lean                         # silent (#guard_msgs)
make check      # exit 0
make test       # all registered contracts: standard logical axioms only
```
