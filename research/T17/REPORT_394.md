# Lane 394 report — T17 U-CAN canonical correction

## 1. What was restated

`NSFormalization.Section3.T17.Correction` now provides the canonical T17
statement layer needed by T18.  `CorrectionAPI` has all 45 reconciled Spec
fields in their original order and with their paper-line docstrings.  Its
placement is T15 U-CAN's raw-field `PlacementData u p f K`; the sole packet
projection in the Spec, `P.velocity`, is `u`, while the profile formulas use
the proved bare `(place.x₀, place.T)` spelling.  `correctionStatement` has the
same existential shape over the raw parameters.

Lane 375 was not present on this base, so the canonical U4
`ForceProfile.lean` source was also restored as a new file.  The already
canonical U3/U2/U5/U6 modules are imported unchanged.

## 2. Lean files and conformance

- `Correction.lean` imports canonical T13/T15/T16 and T17 proof units; it does
  not import `Contracts.*`.
- `correction_canonical.lean` imports the contract layer, carries the literal
  reconciled Spec block under a probe namespace, and provides fieldwise
  adapters for placement, cutoff, local potential, localization, and all 45
  correction fields in both directions.  Both correction conversions have
  round-trip theorems.
- The probe records `rfl` bridges for the fixed cylinder, chart point, the
  three profiles, correction force, and both torus support projections.  It
  closes the landed U3/U4 profile conclusions and U5/U6 derivative bounds by
  `exact` under their stated `hv` and `ε₀≤1` premises.
- `axioms_ucan.lean` audits the new canonical declarations; every printed
  footprint is exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Gaps

This is deliberately a statement-restatement unit and constructs no
`CorrectionAPI` inhabitant.  Per G1, the record field list is unchanged and
contains no `reference_smooth`; T17 assembly must obtain the proved units'
global `hv : ContDiff ℝ ∞ v` premise by chart truncation or by an explicit
assembly theorem hypothesis.

The restored landed U4 theorem proves `force_profile_identity` for the
single-copy chart force.  The record field uses the periodized correction
force; U2's `force_eq` and a local single-copy germ supply that final assembly
bridge.  This lane does not re-prove it, consistently with the no-field-proofs
scope.  The later support, volume, energy, mixed, and Sobolev proof units also
remain outside this lane.

## 4. Commands and results

Run from the worktree after `. scripts/lean-env.sh`, with every Lake command
from `verification/`:

| Command | Result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Correction` | pass, 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T17/Correction.lean` | pass, 0 output |
| `lake env lean ../research/T17/probes/correction_canonical.lean` | pass, 0 output |
| `lake env lean ../research/T17/axioms_ucan.lean` | pass; every declaration reports exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` | pass: plan check, contract/import policy, 13 policy tests, and 45-item work queue |
