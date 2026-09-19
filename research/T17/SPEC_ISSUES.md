# T17 spec / assembly issues (lead log)

- **2026-09-18 10:30Z (lane 370, G1)**: Paper1's `profile_smooth` / `profile_uniform_global_derivative_bound` need **global** `ContDiff ℝ ∞ v`; the reconciled `CorrectionAPI` (`research/T17/Spec.lean`) carries `reference_periodic` only, and T16's `LocalPotentialAPI` gives `v` smooth on the chart cylinder only. Options for U12 (assembly): (a) add `reference_smooth : ContDiff ℝ ∞ v` to `CorrectionAPI` (the reference in `thm:insertion` is a classical solution, smooth on `Ico 0 (T+δ) ×ˢ univ`, so a time-cutoff extension is globally smooth) — a spec amendment to be recorded in RECONCILIATION §3; or (b) re-prove the profile fields through a chart truncation of `v` (`Section3/T16/BallPotential.lean`'s bump argument) so local smoothness suffices. Lead preference: (b) if cheap at assembly, else (a) with the docstring note. Also G3: `PlacementData` cannot be imported into `formalization/` (needs `Contracts.V1.PacketAPI`); canonical units use bare `(x₀, T)`, assembly instantiates `place.x₀`, `place.T`.

## G4 addendum — accepted counterexample and completed block (lane 453 continuation)

The user accepted the geometry counterexample and finalized the amended raw-field
statement with **both** the raw packet support clause
`∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t,x)) ⊆ K`
and `Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius`.
The other premises are exactly `0 < ν`, `0 < r`, `r < 1/2`, `0 < δ`,
`IsPeriodicOn univ v`, `ContDiff ℝ ∞ v`, and vanishing spatial divergence on
`Ioo 0 (place.T + δ) ×ˢ Metric.ball place.x₀ r`.

The former intermediate G4 is disproved in the standalone research probe
`research/T17/probes/assembly_geometry_obstruction_module.lean`, including its
inline axiom audit. It is no longer a canonical module. The completed block is
proved in `Section3/T17/Assembly.lean:correctionStatementAmended_holds` and
registered as `T02.correction`. No further structural fact is assumed:
`place.Kstar_compact`, `place.time_pos`, closure monotonicity followed by
`place.chartBall_in_cube`, T16's `theta_radius_pos`, and
`ε₀ ≤ place.ε₀ ≤ 1` discharge all remaining premises. The 45 fields are unchanged.
