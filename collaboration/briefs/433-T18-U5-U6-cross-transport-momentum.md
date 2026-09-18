# Lane 433-T18-U5-U6-cross-transport-momentum — T18 U5 (the two vanishing cross-transport terms) + U6 (the exact momentum equation of the inserted triple)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/433-T18-U5-U6-cross-transport-momentum` (git branch `erenup/433-T18-U5-U6-cross-transport-momentum`, = lane 426's branch + `origin/erenup/integration-section3`:
`Section3/T18/{Insertion (U1: InsertionData, velocity/pressure/force, formulas), ForceClass (U2), Kinematics (U3), Divergence (U4)}.lean`, the canonical T15 `ScalingAPI` (`Section3/T15/Scaling.lean`,
incl. `solution` = the periodized packet as a classical-solution-like record with `.momentum`, `.divergence`, and the single-copy/support fields), the canonical 45-field T17 `CorrectionAPI`
(`Section3/T17/Correction.lean`: `correction_cancels`/`potential` fields — `Spec.lean:1094` in T18's numbering — `correction_support`, `force_profile_identity`, and the definition of `H_ε = correctionForce`
as the residual of the corrected background), and the T11 canonical modules). Read `CLAUDE.md`, **`research/T18/T18_SPLIT.md` §0, unit U5 (`:98-108`) and unit U6 (`:109-118`)**, the Spec fields
`research/T18/Spec.lean:1838` (`crossTransport_background_advects_packet`: `(b_ε·∇)U_ε = 0` on `Ico 0 T` as `spatialDerivative … = 0`), `:1848` (`crossTransport_packet_advects_background`: `(U_ε·∇)b_ε = 0`),
`:1774` (`momentum`: `navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t,x)` on `Ioo 0 T`), `paper/sections/03-torus.tex:315-328` (`eq:bgzero` and the exactness argument),
`research/T18/REPORT_422.md`, `REPORT_426.md` and `research/T18/probes/{insertion_closes,u2_u4_closes}.lean` (the `InsertionData` conventions and Spec↔canonical conversions), the R³ analogue
`Section4/R42/*` (`Momentum`/`CrossTransport` modules, `LIFESPAN_SPLIT.md`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** — every fact must come from a threaded record field (`ScalingAPI`, `CorrectionAPI`, T11 reference) or the T18 U1–U4 layer. An honest
  partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
- `Section3/T18/CrossTransport.lean` (U5): the two theorems with types = the Spec fields under `InsertionData` projections. Route (`eq:bgzero`): pointwise case split on `x`: on a neighbourhood of
  `supp U_ε(t,·)` the corrected background `b_ε = v + w_ε` vanishes with all derivatives for `t ∈ Ico (T−ε²) T` (`correction.potential.correction_cancels` — read its exact form: it says `w_ε = −v` near
  the packet support, the "cancellation"), so `(b_ε·∇)U_ε` (direction `b_ε = 0`) and `(U_ε·∇)b_ε` (derivative of a field vanishing on an open set) are `0`; off that neighbourhood `U_ε(t,·) = 0` on an
  open set (single-copy support, `scaling.velocity_singleCopy` + placement), so both products vanish; before `T−ε²` the packet is identically zero (pre-activation). Use the vendor locality lemmas
  (`spatialDerivative_congr`-type, `ResidualRegularity`) for "derivative of a field that vanishes near `x` is `0`".
- `Section3/T18/Momentum.lean` (U6): `momentum` under `InsertionData` projections. Route: `reference.momentum` gives `NS(v, π) = g`; the definition of `H_ε` (`correctionForce`) is exactly the residual
  `∂ₜ w_ε − νΔw_ε + (v·∇)w_ε + (w_ε·∇)v + (w_ε·∇)w_ε` so that the corrected background satisfies `∂ₜ b_ε + (b_ε·∇)b_ε − νΔb_ε + ∇π = g + H_ε` (check the exact canonical definition and the
  `force_profile_identity`/`force_eq` bridges; whatever the record supplies is what you use); `scaling.solution.momentum` gives `NS(U_ε, P_ε) = F_ε`; adding and expanding the bilinear advection
  (`advection_add`, `crossAdvection` as in lane 398's six-term expansion in `Section3/T24/AffineMomentum.lean`) reconstructs `NS(u_ε, p_ε)` up to the two cross terms, which vanish by U5; the pressure
  `normalizePressureT (π + P_ε)` has the same gradient as `π + P_ε` (T11 normalization lemma). Deliverables: the two modules, `research/T18/probes/u5_u6_closes.lean` (Spec-form fields discharged via the
  U1 conversions), `research/T18/axioms_u5_u6.lean`, `research/T18/ATTEMPTS_U5_U6.md`, status lines for U5/U6 in `T18_SPLIT.md`. If a field genuinely needs a fact no record carries (e.g. the exact
  cancellation neighbourhood), deliver what closes and record the exact residual statement — do not add a named input.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.CrossTransport NSFormalization.Section3.T18.Momentum` (0 errors), `lake env lean` on each module (0 output), the probe,
the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Try `research/T18/REPORT_433.md`; if the report-file guard blocks it,
put the full report in your final message.
