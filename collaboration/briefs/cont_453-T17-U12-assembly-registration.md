# Lane 453 continuation — T17 U12 assembly + registration with the **completed** G4 hypothesis block (your counterexample is accepted)

Continue in `/data_8T/ping/blowup_density/.claude/worktrees/453-T17-U12-assembly-registration` (branch `erenup/453-T17-U12-assembly-registration`, commit `469f6a36`). Your counterexample is accepted and
recorded (`research/T17/SPEC_ISSUES.md`, G4 addendum): the amended statement must also carry `hball : Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius` and the raw packet support
clause. **Final hypothesis block of `correctionStatementAmended`** (binding):
```
∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField) (K : Set Space) (place : PlacementData u p f K) (v : SpaceTimeField) (r δ : ℝ),
  0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn univ v → ContDiff ℝ ∞ v →
  (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ Metric.ball place.x₀ r, spatialDivergence v t x = 0) →
  (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
  Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius →
  ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧ Nonempty (CorrectionAPI ν place v r δ D)
```
(`IsCompact place.Kstar`, `0 < place.T`, `hcube`, `theta_radius_pos`, `eps_le_one` are derived from the placement/T16 records; if one more structural fact is genuinely underivable, prove a
counterexample as before and stop — otherwise this block is final). Housekeeping: move the counterexample module out of the canonical tree — delete `formalization/NSFormalization/Section3/T17/AssemblyObstruction.lean`
and re-create its content as `research/T17/probes/assembly_geometry_obstruction_module.lean` (a standalone probe; keep `assembly_geometry_obstruction.lean` importing it via `lake env lean` semantics is not
possible for research files, so inline the `#print axioms` into the same probe file) so `formalization/` contains no counterexample modules.
Then carry out the original brief `tmp/codex/briefs/453-T17-U12-assembly-registration.md` deliverables 1–5 in full (canonical `Assembly.lean` with the 45-field record at `correctionData`, `correctionStatementAmended_holds`,
non-vacuity on the cube-centred witness; `Contracts/V1/Correction3.lean` token-for-token + both statements; `Bindings/Correction3.lean`; `Tests/Correction3.lean`; registry `T02.correction` with the hypothesis block in
`scope`; records `ATTEMPTS_U12.md`/`axioms_u12.lean`/`T17_SPLIT.md`/`REPORT_453.md` (append a "Continuation" section)). Ground rules and gates as in the original brief. Report in four parts.
