# Lane 469 — T24b Ub5 / Ub6

## 1. Statements

All four requested fields are proved in `NSFormalization.Section3.T24.RegionsData`
for `assembledVelocity d := finiteVelocitySum (fun j ↦ (d.component j).velocity)`:

- `region_agreement`: equality with component j on its ball for every t in `[0,T)`.
- `region_blowup`: `SpeedUnboundedAtOn d.T` on each prescribed ball.
- `energy_bound`: `(energyEssSupT d.T d.assembledVelocity)^2 ≤
  ENNReal.ofReal (M^2 * ∑ j, d.ε j)`.
- `dissipation_bound`: `(energyGradientT d.T d.assembledVelocity)^2 =
  ENNReal.ofReal (E^2 * ∑ j, d.ε j)`.

Here `E` is the `RegionsData` parameter corresponding exactly to `D` in
`MultipleRegionsAPI`. No enlarged constants or additional inputs are introduced.

Ub5 collapses the finite sum by disjointness. T15's global blow-up theorem
forgets ball membership, so the proof retains the Euclidean scaled witness,
places it in the chart ball using support, then applies single-copy transfer.

Ub6 proves squared Haar slice-norm additivity. The energy argument bounds each
component slice almost everywhere by its essential supremum (T15's identity
is not a constant-in-time slice identity). For gradients, local single-copy
agreement transfers derivatives on the cube interior; scaled topological
support gives vanishing outside the ball. The cube boundary is null. The
rescaled Euclidean dissipation rate supplies the time measurability needed to
interchange the finite sum and the nonnegative integral.

## 2. Files

- `formalization/NSFormalization/Section3/T24/MultipleRegions.lean`: 321 lines,
  15 definitions/theorems, including all four fields and their analytic helpers.
- `research/T24/probes/regions_energy_closes.lean`: all four canonical field
  types instantiated at d, each discharged by `exact`.
- `research/T24/axioms_ub5_ub6.lean`: audits all 15 module declarations.
- `research/T24/ATTEMPTS_UB5_UB6.md`: failed approaches, exact diagnostics,
  resolutions, and the statement checks above.
- `research/T24/T24_SPLIT.md`: Ub5 and Ub6 completion lines.
- `research/T24/REPORT_469.md`: this report.

No existing Lean module was edited. The pre-existing untracked lane brief is
not included in the commit. No dependency on lane 468's Ub4 module is added;
the lead can reconcile the common assembled-velocity definition by `rfl`.

## 3. Gaps and error text

No residual gap or error remains for any of the four fields. No admission,
extra axiom, named analytic input, placeholder, or heartbeat override is used.
All 15 module declarations and all four probe declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

Resolved diagnostics include `Finset.sum_eq_single` failing through the hidden
sum definition, rewrite failures at the definitionally equal placement horizon,
missing `NNReal` scope, an unsolved `essSup_le_of_ae_le` autoParam, nonexistent
`WithLp.sum_apply`/`WithLp.toLp_apply`, an unconstrained implicit centre, and
scaled/parabolic gradient wrapper mismatches. Exact messages and fixes are in
ATTEMPTS. No complete `MultipleRegionsAPI` assembly or Ub4 proof is claimed.

## 4. Commands and results

Every shell used `. scripts/lean-env.sh`; every Lean process used
`LEAN_NUM_THREADS=6`, with Lake's workspace in `verification/`.

- Required closure first:
  `lake build NSFormalization.Section3.T24.MultipleComponents NSFormalization.Section3.T15.Blowup NSFormalization.Section3.T15.Energy`
  — exit 0.
- `lake build NSFormalization.Section3.T24.MultipleRegions` — exit 0,
  0 errors (10051 jobs; existing dependency warnings replayed).
- `lake env lean ../formalization/NSFormalization/Section3/T24/MultipleRegions.lean`
  — exit 0, zero output.
- `lake env lean ../research/T24/probes/regions_energy_closes.lean`
  — exit 0, zero output.
- `lake env lean ../research/T24/axioms_ub5_ub6.lean` — exit 0;
  all 15 entries exactly the standard three axioms.
- Separate probe axiom audit in `tmp/469_probe_axioms.lean` — exit 0;
  all four entries exactly the standard three axioms.
- `make check` — exit 0; 13 policy tests and 45 work-item consistency checks pass.
- `cd verification && lake test` (the `make test` target's Lean command)
  — exit 0; registered contract tests pass.
- `make test-mutations` — exit 0; implementation refactor accepted;
  admitted proof, extra axiom, and weakened hypothesis rejected as required.
- Forbidden-token/heartbeat scan of implementation and probe — no matches.
- `git diff --check` — clean.
