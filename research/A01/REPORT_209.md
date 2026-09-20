# Lane 209 — ManuscriptLocalRegularity

## 1. Theorem proved

`NSFormalization.Section4.A01.manuscriptLocalRegularity_of_pipeline`
proves `ManuscriptLocalRegularity ν a f S w` for any classical solution `w`
with the carrier constructor's exported slice identity and lane 192's all-order
datum paths. The four-field structure is copied verbatim from `Spec.lean`.
All fields use the same horizon, and pressure recovery includes `t = 0`.

## 2. Lean deliverables

New module: `formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean`.
Sobolev datum uniqueness combines finite time orders into one smooth path.
The projected equation follows from momentum and the tensor-divergence bridge.
Pressure recovery is proved for every classical solution with admissible force:
`div ∂ₜu = 0` and `div Δu = 0` give the interior identity, and continuity of
spatial divergence gives the initial endpoint. The existing `PressureGauge`
theorem supplies the radial-potential gauge for that same solution.

`axioms_manuscript_regularity.lean` checks every new declaration and constructs
an actual regular solution through the complete 207 → 192 → 190/189 → 180
pipeline, including a concrete zero-data example. All eleven audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`. Attempts and the lane-209
split row are recorded. No existing Lean module was edited.

## 3. Remaining scope

No new analytic input or regularity gap remains in this lane. Lane 208's
`LocalSolution.lean` is absent from this checkout, so the requested arbitrary
constructor-output interface is used. Its consumer supplies `w`, `hf`, `U`,
`hslice`, and `hpaths`; no pressure-construction equality is required.
The separate H¹-uniform horizon bound and registration of `LocalTheoryAPI`
remain outside this delivery. No merge, rebase, or push was performed.

## 4. Validation

After sourcing `scripts/lean-env.sh`, all Lake commands run from `verification/`
with `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section4.A01.ManuscriptRegularity`: passed;
  existing dependency warnings are replayed. The new module has no diagnostics.
- `lake -q --log-level=error build NSFormalization.Section4.A01.ManuscriptRegularity`:
  passed, zero output (suppresses replayed dependency warnings).
- `lake env lean ../formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean`:
  passed, zero output.
- `lake env lean ../research/A01/axioms_manuscript_regularity.lean`: passed;
  eleven exact standard-axiom lists and no diagnostics.
- `make check`: passed, including architecture, 13 Python tests, and work queue.
- `git diff --check`: passed. Verbatim structure comparison and prohibited-token
  scan of the two new Lean files passed.

Raw gate logs are local ignored files under `tmp/209-*`; they are not committed.

## Review note applied (2026-09-16, lead)

Lane 208's chosen `localSolution` (merged as #213) exposes only the `ClassicalSolutionR`; to instantiate `manuscriptLocalRegularity_of_pipeline` for it, the carrier witnesses (`U`, `hslice`, `hpaths`) must be preserved alongside the chosen solution (a bundling structure or a transfer theorem) — this is lane 211's job. The authorized constructor-output interface of this lane is unchanged.
