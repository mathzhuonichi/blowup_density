# Lane 496 — bounded-domain Proposition 3.16 specification

## 1. Statements

Added `MultipleRegionsOmegaAPI` and `multipleRegionsOmegaStatement` in research
(packet-indexed) and canonical (raw packet hypotheses) forms. Exactly 30 fields:
29 retained names and explicit `no_slip` replacing torus-only `scaling`.
The prescribed Ω satisfies the owner's bounded-box-or-smooth-domain predicate;
ball closures lie in Ω and the balls are pairwise disjoint. Components are
un-periodised scaled packets starting at `T − ε_j²`, from rest, without a
background. Pressure is normalized over Ω to match `ClassicalSolutionOmega`.
The sum has separate `SpeedUnboundedAtOn` clauses, restricted physical L² energy
bound (≤) and full-gradient dissipation identity (=), with original M,D.
Every field cites revised article lines 511–535; gauge vocabulary is at 458.

## 2. Files

- `research/T24/SpecOmega.lean`: registered packet-indexed research specification.
- `formalization/NSFormalization/Section3/T24/MultipleOmega.lean`: canonical raw
  record and definitions only; no imports of `Contracts.*`.
- `research/T24/probes/multiple_omega_spec_closes.lean`: 30 domain field examples,
  18 shared torus field examples, concrete Ω=(0,1)^3 and N=1 specialization.
- `research/T24/COMPARISON_OMEGA.md`: complete change/drop ledger and norm choices.
- `research/T24/T24_SPLIT.md`: P5.1–P5.5 targets and suppliers for proof lane 497
  and assembly/registration lane 498.
- `research/T24/ATTEMPTS_496.md`: scope and gate diagnostics.

## 3. Gaps and exact diagnostics

This is a specification, not an existence proof. The probe assumes an API
variable; it does not construct a solution or prove non-vacuity. All analytic
proof units, assembly and `T04.multiple_regions_v2` registration remain for the
subsequent lanes. `M316_B` remains Partial with its original completion inputs.

The only failing gate is manifest reachability:
```
AssertionError: Unreferenced Lean modules: ['NSFormalization.Section3.T24.MultipleOmega']
make: *** [Makefile:4: check] Error 1
```
A one-line addition to `entrypoints.json` is needed, but falls outside the stated
research-files-plus-one-canonical-module scope. Clarification has been requested;
no proof status or contract registry has been changed.

## 4. Commands and results

Source `. scripts/lean-env.sh`; run Lake from `verification/` with
`LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T24.MultipleOmega`: PASS (10131 jobs;
  existing dependency warnings replayed, new module has no diagnostic).
- `lake env lean ../research/T24/SpecOmega.lean`: PASS, 0 output.
- `lake env lean ../research/T24/probes/multiple_omega_spec_closes.lean`: PASS,
  0 output (49 examples).
- `make check` from the worktree root: FAIL at the exact manifest gate above.
- `python3 experiments/check_contracts.py --summary`: PASS, 29 contracts.
- `python3 experiments/test_contract_policy.py`: PASS, 11 tests.
- Textual comparison after expanding the research packet projections: PASS,
  all 30 canonical/research field types match.
- `git diff --check`: PASS; prohibited proof tokens absent from new Lean files.

## Lead note (2026-09-21 04:00Z)
Spec accepted after comparison with `Spec.lean:1176-1333` and revised `03-torus.tex:511-535`: dropping `scaling` (no periodisation) and adding `no_slip` are the right domain changes; `energyEssSupOmega`/`energyGradientOmega` use the registered restricted physical norms. Lead micro-edit: `entrypoints.json` now lists `NSFormalization.Section3.T24.MultipleOmega` so that `make check` (module reachability) passes on the core branch; the proof lanes 497/500 and the registration lane 501 follow the "P5 units" split.
