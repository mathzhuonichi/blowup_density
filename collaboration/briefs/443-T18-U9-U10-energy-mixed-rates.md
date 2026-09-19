# Lane 443-T18-U9-U10-energy-mixed-rates — T18 U9 `energyRate` (`eq:Eclose`) + U10 mixed-norm closeness (`eq:Fclose`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/443-T18-U9-U10-energy-mixed-rates` (git branch `erenup/443-T18-U9-U10-energy-mixed-rates`, based on `origin/erenup/integration-section3`: the T18
layer `Section3/T18/{Insertion (U1: InsertionData with the threaded raw packet fields P.energyBound/dissipationBound, scaling : ScalingAPI, correction : CorrectionAPI, reference), ForceClass (U2),
Kinematics, Divergence, CrossTransport, Momentum}.lean`, and the canonical records `Section3/T15/Scaling.lean` (`ScalingAPI` fields `energySlices_memLp`, `packetEnergyIdentity`,
`packetDissipationIdentity`, `mixed_memLp`, `packetMixedScaling`, `force_mem`), `Section3/T17/Correction.lean` (`CorrectionAPI` fields `energyConst`, `energyConst_nonneg`,
`correction_energy_bound`, `correction_slice_memLp`, `correction_gradient_memLp`, `force_spatial_memLp`, `mixedConst`, `mixedConst_nonneg`, `force_mixed_bound`), `Section3/T10/PeriodicData.lean:328-340`
(`energyEssSupT`/`energyGradientT`/`energyENormT`), the torus mixed norm `mixedLebesgueENormT`/`MemMixedLebesgueT` (grep T10/T11), `Contracts.V1.alpha` and its canonical copy). **All facts you need are
fields of the threaded records** — U9/U10 are bookkeeping over them. Read `CLAUDE.md`, **`research/T18/T18_SPLIT.md` §0, unit U9 (`:173-179`) and unit U10 (`:181-188`)**, the Spec fields
`research/T18/Spec.lean:1888-1925` (`energyRate`, `forceDiffMixedConst`, `forceDiffMixedConst_nonneg`, `forceDifference_mixed_memLp`, `forceDifference_mixed_bound`), `research/T18/REPORT_{422,426,433}.md`
and probes (`InsertionData` conventions and Spec↔canonical conversions), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
Two new modules (namespace `NSFormalization.Section3.T18`), theorem types = Spec fields under `InsertionData` projections:
- `Section3/T18/EnergyRate.lean` (U9): `energyRate` — `u_ε − v = w_ε + U_ε`; prove the triangle inequality for `energyENormT place.T` (`essSup` of a sum ≤ sum of essSups via `eLpNorm_add_le`
  on the slices — the `MemLp` slice guards come from `scaling.energySlices_memLp` and `correction.correction_slice_memLp`/`correction_gradient_memLp`; `lintegral` of the gradient square: use
  `eLpNorm`-form or `(a+b)² ≤ 2a²+2b²`-free Minkowski in `ℝ≥0∞` via `eLpNorm_add_le` at exponent 2 on the space-time gradient — pick the spelling that matches `energyGradientT`), then
  `‖U_ε‖ = (M + D) ε^{1/2}` from `packetEnergyIdentity` + `packetDissipationIdentity` and `‖w_ε‖ ≤ energyConst·ε^{3/2}` from `correction_energy_bound`.
- `Section3/T18/MixedRate.lean` (U10): `forceDiffMixedConst p q := mixedConst p q + ‖F‖_{L^q_tL^p_x}`-type real constant (read the Spec bound: `≤ C_{p,q}(ε^{α} + ε^{α+1})` with `α = alpha p q`),
  `_nonneg`, `forceDifference_mixed_memLp` (`g_ε − g = H_ε + F_ε`: time-path guards `scaling.mixed_memLp` + the `H_ε` path from `correction.force_spatial_memLp` — check whether the record gives a
  time-path or only slices; if only slices, build the path from continuity + compact time support as lane 439 did in `Section3/T15/Mixed.lean` §3 (`torusSlicePath`) — that module is on lane 439's
  branch, not this base: reprove locally if needed), `forceDifference_mixed_bound` (triangle for `mixedLebesgueENormT` + `packetMixedScaling` + `force_mixed_bound`).
Deliverables: the two modules, `research/T18/probes/u9_u10_closes.lean` (Spec-form fields via the U1 conversions), `research/T18/axioms_u9_u10.lean`, `research/T18/ATTEMPTS_U9_U10.md`, status lines
in `T18_SPLIT.md`. If one field needs a fact no record carries (say exactly which), deliver the others and record the exact residual.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.EnergyRate NSFormalization.Section3.T18.MixedRate` (0 errors), `lake env lean` on each module (0 output), the probe,
the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T18/REPORT_443.md`.
