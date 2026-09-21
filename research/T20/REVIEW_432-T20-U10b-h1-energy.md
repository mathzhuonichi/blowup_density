ACCEPT-WITH-NOTES

## What the lane claims

The lane claims `CH1 = 2` and a theorem `hOneEnergy` for zero initial data, `g ∈ forceClassT`, `criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν)`, and interior `t`, concluding an actual derivative of `gradientSqT` plus `ν * laplacianSqT` bounded by `CH1 * ν⁻¹ * lTwoSqT`; this matches the paper's H¹ estimate (`paper/sections/03-torus.tex:467-484`). The exact theorem is at `formalization/NSFormalization/Section3/T20/H1Energy.lean:404-419`, with `CH1` at `:357` and `criticalSmallnessH1` at `:368`. The probe reproduces the canonical field type and exact instantiation (`research/T20/probes/h1_energy_closes.lean:35-50`).

## What is in Lean

The order-2 Laplacian Parseval bridge is proved at `H1Energy.lean:108-151`; the frequency derivative and tsum assembly are present before the final theorem. The constants are positive and the radius has both strict quarter bounds (`:370-392`). The non-vacuity probe supplies the zero-force/zero-solution instance and proves the strict smallness hypothesis (`h1_energy_closes.lean:80-140`). No named placeholder or vacuous `True` theorem was found.

## Gaps

No mathematical gap found. A substantive mutation changing the RHS constant from `CH1` to `1` was tested in `research/T20/probes/rev432_negative.lean`; Lean rejects `exact hOneEnergy` with a type mismatch, displaying the original `CH1 * ν⁻¹ * ...` versus `1 * ν⁻¹ * ...`. Whole-tree search found no competing `hOneEnergy` or order-2 Parseval lemma under `formalization/NSFormalization/Section4`.

One process note: the worker report says `make check` passed; rerunning from the repository root passed, while running it from `verification/` (the wrong directory) correctly reports “No rule to make target 'check'”. The report should state the root working directory explicitly.

## Commands and results

From the repository root, with `. scripts/lean-env.sh` and `LEAN_NUM_THREADS=6`:

- `cd verification && lake build NSFormalization.Section3.T20.H1Energy`: `Build completed successfully (10654 jobs)` (only replayed upstream warnings).
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T20/H1Energy.lean`: exit 0, 0 bytes.
- `cd verification && lake env lean ../research/T20/probes/h1_energy_closes.lean`: exit 0, 0 bytes.
- `cd verification && lake env lean ../research/T20/axioms_u10b.lean`: 31/31 declarations list exactly `[propext, Classical.choice, Quot.sound]`.
- `make check`: exit 0; contract and queue checks pass. `scripts/gates.sh NSFormalization.Section3.T20.H1Energy` and `python3 verification/check_contracts.py --base-ref origin/erenup/integration-section3` complete successfully (the gate output includes the existing repository-wide copied-source warning inventory).
- `rg -n 'sorry|admit|axiom|native_decide' H1Energy.lean`: only the documentation sentence denying those tokens.
- `git diff --name-only origin/erenup/integration-section3...HEAD`: the new lane module/records plus the lane's documented shared-note updates; no pre-existing Section3 theorem was edited.

