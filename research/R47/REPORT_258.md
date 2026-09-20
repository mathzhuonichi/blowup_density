# Lane 258 — R47 assembly

## 1. Theorem proved

`rGrid_choose_of_realization (hreal : CompactHomogeneousRealization)` proves
Theorem 4.7 in the exact `RGridAPI.choose` shape. `RGridFamily` and `RGridAPI`
are copied byte-for-byte from `research/R47/Spec.lean`; the theorem statement
matches `choose` token for token. Every field is filled on one family and one
positive-radius ball contained in a cell of each prescribed grid.

## 2. Lean deliverables

- `verification/Bindings/GridAssembly.lean`: `rGridFamily_of_data` and the
  universal theorem, using the supplied reference and an arbitrary-ball
  reconstruction of lane 233's insertion chain. A fixed admissible scale
  supplies the total extension outside the scale interval.
- `verification/Bindings/GridAssemblyNorms.lean`: compact-force mixed and
  homogeneous triangle inequalities, positive-power limits, and both force
  convergence suppliers. The literal mixed norm is proved directly; no
  order-zero norm bridge is assumed. Pressure uses the zero gauge.
- `research/R47/axioms_assembly.lean`: all seven implementation declarations
  print exactly `[propext, Classical.choice, Quot.sound]`; concrete zero-data
  examples have `ν=T=δ=1`, `a=g=0`, and respectively zero grids and one unit grid.
- `ATTEMPTS_ASSEMBLY.md` records successful and rejected routes;
  `COMPARISON.md` records the proved scope and supplier boundary.

No existing Lean module, contract, test, or specification was edited. No
heartbeat override or additional proof assumption was introduced.

## 3. Remaining input

Only lane 250's exact `CompactHomogeneousRealization` remains, exclusively for
`L²_tḢ⁻¹_x` force convergence. Lane 255 is assigned to prove it. The assembly
is conditional on that input and does not claim unconditional Theorem 4.7.
The general `H⁰=L²` norm bridge remains outside this lane and is unnecessary
for its direct mixed-norm convergence proof.

## 4. Validation and commit

After sourcing `scripts/lean-env.sh`, from `verification/` where applicable:

- `LEAN_NUM_THREADS=6 lake build Bindings.GridAssembly`: PASS. Lake replays
  existing dependency warnings; the new modules emit no warnings. Thus the
  ordinary build is successful but not literally silent.
- `LEAN_NUM_THREADS=6 lake env lean Bindings/GridAssembly.lean`: PASS, zero output.
- `LEAN_NUM_THREADS=6 lake env lean Bindings/GridAssemblyNorms.lean`: PASS, zero output.
- `LEAN_NUM_THREADS=6 lake env lean ../research/R47/axioms_assembly.lean`: PASS;
  exactly seven standard-axiom reports, and all examples accepted.
- `make check`: PASS; `LEAN_NUM_THREADS=6 make test`: PASS.
- `make test-mutations`: PASS, including all expected rejections.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`:
  PASS, base compatibility checked.
- Text comparison: both structures byte-identical; `choose` token-identical.
- `git diff --check`: PASS.

Committed on `erenup/258-R47-assembly` with subject
`[258-R47] Assemble grid theorem conditional only on homogeneous realization`.
No push, merge, or rebase was performed. Local gate logs are under
`tmp/258-R47/` (untracked build artifacts).
