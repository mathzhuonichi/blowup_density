# Lane 384 report — T15 U-CAN canonical scaling

## 1. What was restated

`NSFormalization.Section3.T15.Scaling` now contains the formalization-side T15
statement layer over raw packet fields.  It has:

- `PlacementData u p f K`, with all **17** fields of
  `research/T15/Spec.lean:560-643`;
- `ScalingAPI (ν := ν) u p f K M D place`, with all **21** fields of
  `Spec.lean:654-909`, in the same order and with the paper-line docstrings;
- `scalingStatement`, replacing the selected `PacketImportAPI` by the seven
  raw data parameters `u,p,f,K,M,D,τ`, the positive-viscosity premise, all
  **26** `PacketAPI` clauses, and both `PacketEnergyAPI` clauses;
- the honest mixed-Lebesgue/Sobolev/energy carrier definitions needed by the
  field types, copied onto canonical T10/T13/Section 4 vocabulary.

The complete raw-to-contract table is in `ATTEMPTS_UCAN.md`.  In short,
`P.velocity/pressure/force/carrier/energyBound/dissipationBound/quietTime` map
to `u/p/f/K/M/D/τ`; every propositional projection maps to an explicitly typed
arrow of `scalingStatement`.  No premise was replaced by a free `Prop`.

## 2. Lean files and conformance

- `formalization/NSFormalization/Section3/T15/Scaling.lean` is the canonical
  module.  It imports no `Contracts.*`; it reuses lane 362's
  `scaledVelocity`, `scaledPressure`, `scaledForce`, periodization and pressure
  normalization, plus T13's canonical `LocalizationAPI`.
- `research/T15/probes/scaling_canonical.lean` imports
  `Contracts.V1.Packet` and `Contracts.V1.PacketImport`, then restates the two
  Spec structures.  The copied block is byte-for-byte identical to
  `Spec.lean:560-909` apart from its enclosing namespace.  It supplies
  `placementOfSpec`/`placementToSpec` and `ofSpec`/`toSpec`, names every field
  in both directions, and proves both pairs of round trips.
- The probe proves ten definitional drift bridges by `rfl`:
  `scaledStartTime`, `scaledSourcePoint`, the three `scaled*` definitions, the
  three `periodizedScaled*` definitions, `normalizedScaledPressure`, and
  `alphaT`.  The four visible packet-to-raw argument changes are velocity,
  pressure, force, and normalized pressure.
- `research/T15/axioms_ucan.lean` audits every canonical declaration.
- `research/T15/T15_SPLIT.md` records the completed U-CAN unit.

## 3. Gaps

There is no statement or conversion gap against this lane's brief.  This is
deliberately a statement-restatement unit: it constructs no `ScalingAPI`
inhabitant and proves none of its 21 analytic fields.  Those remain the T15
U2--U15 proof campaign described in `T15_SPLIT.md`.  No contract was registered
or changed, and no existing formalization module was edited.

## 4. Commands and results

Run from the worktree with `. scripts/lean-env.sh`, and all `lake` commands
from `verification/`:

| Command | Result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Scaling` | pass, 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T15/Scaling.lean` | pass, 0 output |
| `lake env lean ../research/T15/probes/scaling_canonical.lean` | pass, 0 output |
| `lake env lean ../research/T15/axioms_ucan.lean` | pass; every line reports exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` | pass: plan check, contract/import policy, 13 policy tests, and 45-item work queue |
