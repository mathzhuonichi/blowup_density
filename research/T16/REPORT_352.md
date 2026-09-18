# Lane 352 report — T16 gap 2: the unit-periodic lattice lift

## 1. What was proved

The seven `correction_*` fields of the canonical `LocalPotentialAPI`
(`formalization/NSFormalization/Section3/T16/LocalPotential.lean`) as lemmas about
the unit-periodic lift `latticeLift w z = ∑' k, w (z.1, z.2 − latticeVector k)`
of a chart correction `w` (smooth on `ℝ×ℝ³`, spatial slice support in `ball x₀ ρ`,
`ρ < 1/2`).  All in `Section3/T16/LatticeLift.lean`, every declaration
`[propext, Classical.choice, Quot.sound]`.  Load-bearing statements:

- `latticeLift_eq_periodize (w) : latticeLift w = NavierStokes.PeriodicLocalization.periodize w := rfl`
- `latticeLift_smooth (hcd : ContDiff ℝ ∞ w) (hsupp : ∀ z, w z ≠ 0 → z.2 ∈ ball x₀ ρ) : ContDiff ℝ ∞ (latticeLift w)`
- `latticeLift_periodic (w) : IsPeriodicOn univ (latticeLift w)`
- `latticeLift_eq_of_ball (hslice : ∀ t y, w (t,y) ≠ 0 → y ∈ ball x₀ ρ) (hρr : r + ρ ≤ 1) (hx : x ∈ ball x₀ r) : latticeLift w (t,x) = w (t,x)`
- `latticeLift_divergence_zero (hcd) (hsupp) (hdivw : ∀ t x, spatialDivergence w t x = 0) (t x) : spatialDivergence (latticeLift w) t x = 0`
- `latticeLift_timeSupport (hcs : HasCompactSupport w) (htsupp : tsupport w ⊆ Ioo a b ×ˢ univ) : tsupport (latticeLift w) ⊆ Ioo a b ×ˢ univ`
- `latticeLift_sliceSupport (hslice) (hρr : ρ < r) (t) : tsupport (fun x => latticeLift w (t,x)) ⊆ periodicSet (ball x₀ r)`
- `latticeLift_cancels (hv_per : IsPeriodicOn univ v) (hslice) (hρr : r+ρ ≤ 1) (hcancel : ∀ x ∈ ball x₀ r, v (t,x)+w (t,x)=0) (hpacket : tsupport (fun x => P x) ⊆ periodicSet (ball x₀ r)) : ∃ O, IsOpen O ∧ tsupport (fun x => P x) ⊆ O ∧ ∀ x ∈ O, v (t,x)+latticeLift w (t,x)=0`
- `correction_fields_of_chart (…) : <conjunction of the seven canonical field bodies for `fun ε => latticeLift (W ε)`>` — packaging for lane 353.

`latticeLift_eq_periodize` is the crux: `latticeVector = lattice` by `rfl`, so the
lift is definitionally OpenAI's `periodize`, and all of
`NavierStokes.PeriodicLocalization` is reused verbatim.

## 2. What exists in Lean now

- New module `formalization/NSFormalization/Section3/T16/LatticeLift.lean`
  (namespace `NSFormalization.Section3.T16`), 19 declarations, green.
- Probe `research/T16/probes/lattice_lift_closes.lean`: the seven canonical field
  types verbatim (projected from `correction_fields_of_chart`) + a nonzero smooth
  bump whose lift is nonzero and periodic.  Compiles.
- `research/T16/axioms_lattice_lift.lean`: `#print axioms` on all 19 decls, all
  `[propext, Classical.choice, Quot.sound]`.
- Records: `research/T16/ATTEMPTS_LATTICE_LIFT.md`, `COMPARISON.md` status line.

## 3. Gap

- **Not this lane:** T16 gap 1 (`potential_smooth`/`potential_curl` for general
  local `v`) is untouched (see `ATTEMPTS.md` §Gap 1).
- The packaged `correction_fields_of_chart` takes as hypotheses the chart-level
  facts about the correction family `W` (smoothness, compact support,
  divergence-freeness, the product support bound, the curl formula, the ball
  cancellation) and the T14 packet-support bound.  Discharging those for the
  concrete `W ε = physicalCorrection v x₀ T θ η ε` is lane 353's assembly job
  (the chart facts `localCorrection_*` / `exists_local_background_removal` in
  `Paper1/LocalCutoff.lean` produce exactly this shape).  No stub, no `sorry`,
  no placeholder `Prop` field was introduced; the transport itself is complete.
- `LocalPotentialAPI` has **seven** `correction_*` fields, not eight (the brief
  double-counts `support`/`support_ball`).

## 4. Commands run and results

- `. scripts/lean-env.sh` (every shell).
- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.LatticeLift`
  → `Build completed successfully (9358 jobs).` (0 errors)
- `lake env lean ../formalization/NSFormalization/Section3/T16/LatticeLift.lean` → 0 errors.
- `lake env lean ../research/T16/probes/lattice_lift_closes.lean` → exit 0, 0 errors.
- `lake env lean ../research/T16/axioms_lattice_lift.lean` → all 19 decls
  `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` (worktree root) → contract-policy tests OK (13 passed),
  work-queue consistent.
