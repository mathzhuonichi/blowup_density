# Lane 415-T20-U8-critical-energy — T20 U8: `criticalEnergy` verbatim (`eq:criticalenergy`, the differential inequality for `y² = ‖v‖²_{Ḣ^{1/2}}`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/415-T20-U8-critical-energy` (git branch `erenup/415-T20-U8-critical-energy`, based on lane 413's branch merged with
`origin/erenup/integration-section3`: it contains `Section3/T20/{CriticalRegularity,MeanReduction,BIntegral,ConstantTransport,CriticalTrilinear}.lean` — lane 413's
`criticalTrilinear`/`criticalTrilinear_pairing`/`advection_eq_slice` (U8 bridges, `rfl`), lane 389's `meanFreeEquation` and mean-reduction fields, lane 390's
`constantTransportSkew`/`bIntegral` — and the T11/T12 modules). Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0 and unit U8** (target verbatim: the field
`criticalEnergy` of `Section3/T20/CriticalRegularity.lean:286-299`, `eq:criticalenergy` `paper/sections/03-torus.tex:425-440`), `research/T20/REPORT_413.md` (§1 and the
U8 shape check in `research/T20/probes/critical_trilinear_closes.lean` §3), `REPORT_389.md`/`REPORT_390.md`, `Section3/T11/EnergyIdentity.lean:434`
(`hasDerivAt_torusSobolevNormAt_sq` — the order-1 analogue of the derivative of `y²`), `Section3/T11/HighOrder.lean:312` (`torusPressureDrop`), the R³ analogue
`Section4/R43/CriticalMomentum.lean` (`rcritical1_of_classical'`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T20/CriticalEnergy.lean` (namespace `NSFormalization.Section3.T20`): `theorem criticalEnergy` whose type is literally the
canonical field (check with `example : <field type> := criticalEnergy`): for `0 < ν`, `g ∈ forceClassT`, `w : ClassicalSolutionT ν 0 g T`, every `t ∈ Ioo 0 T`,
`∃ E', HasDerivAt (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2) E' t ∧ E'/2 + (ν − C₀·y(t))·z(t)² ≤ b(t)·y(t)` with `C₀ := criticalTrilinearConst` (413).
Route (U8): (1) differentiate `y(s)² = ‖v(s)‖²_{Ḣ^{1/2}}` along the classical solution — mirror `hasDerivAt_torusSobolevNormAt_sq` at order 1/2 (the Fourier-side derivative
through the datum path; read how `criticalY` is built on `periodicHomogeneousENorm` and what regularity `reductionRegular` (U1) supplies); (2) pair the mean-free equation
`meanFreeEquation` (U6) against `Λv`: the pressure term drops (`div Λv = 0`, `torusPressureDrop`), the constant transport term cancels (`constantTransportSkew` at `w = Λv`),
the dissipation gives `+ν z(t)²` (`⟪−νΔv, Λv⟫ = ν‖v‖²_{Ḣ^{3/2}}` on the Fourier side), the nonlinear term is bounded by `criticalTrilinear_pairing` (413), and the force term
`|⟪h, Λv⟫| = |⟪Λ^{1/2}h, Λ^{1/2}v⟫| ≤ b(t)·y(t)` (Cauchy–Schwarz on the coefficient side). If one of these identities (e.g. the Fourier-side dissipation identity or the
`Ḣ^{1/2}` derivative formula) is genuinely missing and heavy, deliver every other step as separate theorems with the exact residual statement and error text, and close the
field under that single explicit residual **in the probe only** (never as a named input in the module). Deliverables: the module, `research/T20/probes/critical_energy_closes.lean`
(field-type match by `exact`; non-vacuity: instantiate at a concrete classical solution if the tree has one — grep `ClassicalSolutionT` witnesses in `Section3/T11`/T24 probes — else
at the zero force with the zero solution), `research/T20/axioms_u8.lean`, `research/T20/ATTEMPTS_U8.md`, U8 status line in `T20_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalEnergy` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Try `research/T20/REPORT_415.md`; if the
report-file guard blocks it, put the full report in your final message.
