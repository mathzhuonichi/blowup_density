# REPORT — lane 332 (T11 / U13, `restartBeyond`)

Branch `erenup/332-T11-U13-restart-beyond`. Takeover of a codex run that died mid-file; the
uncommitted 375-line partial was read, its correct half kept, its two broken declarations replaced
(details and exact error text in `research/T11/ATTEMPTS_RESTART_BEYOND.md`).

## 1. Which theorem is proved

`restartBeyond`, the third field of `PeriodicContinuationAPI`, **verbatim** as written in
`research/T11/probes/api_on_canonical.lean` — `∃ δ > 0` quantified *before* the datum, so `δ` is
uniform over the `H¹` ball `K`:

> for `ν > 0`, `f ∈ forceClassT`, `S > 0` and `K ≠ ⊤` there is `δ > 0` such that for every
> `a ∈ initialClassT` and every pair `(u, p)` with `SolvesBelowT ν a f S u p` whose velocity
> satisfies `periodicSobolevENorm 1 (u(t,·)) ≤ K` on `[0, S)`, there is a
> `ClassicalSolutionT ν a f (S + δ)` whose velocity and pressure agree with `u` and `p` pointwise
> on `[0, S) × T³`.

It is conditional on exactly one named hypothesis, `PeriodicQuantitativeLocalInput'`
(`Section3/T11/LocalExistence.lean:24`), consumed only through lane 321's `restart`. The module
introduces no new `def … : Prop`.

Mathematical content: `δ` comes from `restart` at the ball `K` for the fixed `f, S`; the basepoint
is `t₀ = max 0 (S − d/2) ∈ [0, S)`, chosen so that `t₀ + d = S + δ`; the restart is taken from the
velocity slice `u(t₀, ·)` — an admissible datum by `velocitySlice_mem_initialClassT` — with the
shifted force `timeShiftT t₀ f`; the two charts are pasted at the seam `(t₀ + b)/2` strictly inside
their overlap; and the extension of the agreement from the first chart to all of `[0, S)` uses lane
315's `velocity_unique`/`pressure_unique` against a second `SolvesBelowT` chart chosen past each
time `t`.

## 2. What is in Lean now

`formalization/NSFormalization/Section3/T11/RestartBeyond.lean` (namespace
`NSFormalization.Section3.T11`), 12 declarations, no `sorry`/`axiom`/`native_decide`, no
`maxHeartbeats` override:

| declaration | statement |
|---|---|
| `velocity_hasDerivAt_timeT` | the velocity slice `ρ ↦ u(ρ,x)` has derivative `∂ₜu(s,x)` at interior `s` (torus port of `Section4.C01.velocity_hasDerivAt_time`) |
| `velocitySlice_mem_initialClassT` | `(fun x => w.velocity (b,x)) ∈ initialClassT` for `b ∈ [0,T)` |
| `restrictClassicalSolutionT` (+ 2 `rfl` projections) | a solution restricts to any shorter positive horizon with the same fields |
| `solvesBelowT_of_classicalSolutionT` | `SolvesBelowT ν a f T w.velocity w.pressure` |
| `shiftedSolutionT` | `ClassicalSolutionT ν (u(b,·)) (timeShiftT b f) (T − b)` from a solution and `b ∈ [0,T)` |
| `restartedResidualT` | a solution of the `b`-shifted problem satisfies the original residual on the original clock |
| `shifted_velocity_uniqueT`, `shifted_pressure_uniqueT` | common-interval agreement **without** the `initialClassT`/`forceClassT` hypotheses |
| `glueClassicalSolutionT` | **exported constructor** for U14/U16: `w` on `[0,T)` + restart `w₂` from `u(b,·)` with `T < b + L` give `∃ v : ClassicalSolutionT ν a f (b+L)` agreeing with `w` on all of `[0,T)`, in both velocity and pressure |
| `restartBeyond` | the API field above |

Plus a non-vacuity `example`: the nonzero forced witness of `LocalExistence` really does glue into a
classical solution on the longer horizon whose velocity at the origin is nonzero.

Two structural differences from the `R³` model (`Section4.A04.ShiftedExtension`) are settled here:

- **exact pressure agreement** ("needs a lemma" ⑩). `ClassicalSolutionT` carries the Haar gauge
  `∫_{T³} p(t) = 0` as a structure field, so both charts are already normalized and Paper 1's
  `normalized_flows_agree` gives equality of the pressures, not merely of their gradients. The
  `R³` basepoint normalization `w.normalizePressure 0` is not used and not needed.
- the three extra T10 fields are pasted as well: the integer-order Fourier path via `datum_unique`
  on the overlap, the torus pressure-gradient `MemLp` and the gauge slicewise.

The type-generic overlap calculus (`overlapPaste`, `overlapPaste_left/right`, `contDiffOn_overlap`,
`continuousOn_overlap`, `residual_eq_of_local_slices`) is reused verbatim from `Section4.A04`
rather than restated — the partial's ~50 duplicated lines were deleted.

Other files: `research/T11/probes/restart_beyond_closes.lean` (the verbatim target plus five export
shapes and two non-vacuity witnesses), `research/T11/axioms_restart_beyond.lean` (`#guard_msgs` on
all 12 declarations), `research/T11/ATTEMPTS_RESTART_BEYOND.md`, one appended status line in
`research/T11/T11_SPLIT.md` §1.

## 3. What is missing

- **The one named input remains named.** `restartBeyond` is a conditional theorem under
  `PeriodicQuantitativeLocalInput'`; U9 is what discharges it. Nothing else is assumed.
- **`ExtendsBeyondT` is not claimed here.** The output of `restartBeyond` *is* the payload of
  `ExtendsBeyondT ν a f S u p` (`LocalTheory.lean:68`), but wiring it needs the `H¹` trajectory
  bound from U12 at `m = 1`; that is U14's job and is out of scope for this lane.
- **No `maximalLifespanT` statement.** `ENNReal.ofReal (S + δ) ≤ maximalLifespanT ν a f` follows in
  one line from the produced solution (`le_iSup_of_le`), but the target field asks for the concrete
  solution with agreement, so only that is proved.
- `shifted_velocity_uniqueT`/`shifted_pressure_uniqueT` duplicate lane 315's statements minus two
  unused hypotheses. If U17 prefers a single spelling, lane 315's `Uniqueness.lean` could drop
  `ha`/`hf` instead; that would be an edit to a landed module and was not done here.

## 4. Commands run and results

| command | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.RestartBeyond` | `Build completed successfully (10562 jobs)`, 0 errors, 0 warnings from this module |
| `cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/RestartBeyond.lean` | no output, exit 0 |
| `cd verification && lake env lean ../research/T11/probes/restart_beyond_closes.lean` | no output, exit 0 |
| `cd verification && lake env lean ../research/T11/axioms_restart_beyond.lean` | no output, exit 0 — all 12 declarations print exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` (worktree root) | exit 0; contract architecture, policy tests (13), work-queue consistency all pass |
| `make test` (worktree root) | all registered contracts replayed: "checked; standard logical axioms only" |
