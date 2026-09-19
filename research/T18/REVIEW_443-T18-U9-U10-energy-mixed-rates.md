ACCEPT

## 1. What the lane claims

The final (continuation) claim is that U9 supplies the canonical energy rate
with the two lead-approved raw sign premises, and that U12/Spec assembly
discharges those premises from the registered packet.  U10 claims the real
mixed-rate constant, its nonnegativity, an honest mixed Bochner path, and the
mixed-rate bound.  The report explicitly says that its earlier parameter-free
U9 residual is superseded (`research/T18/REPORT_443.md:190-198`) and reports 24
audited public declarations after adding `energyRate`
(`research/T18/REPORT_443.md:200-213`).

These are the mathematical statements requested by the brief.  The paper has

```text
paper/sections/03-torus.tex:299-303
 ||u_eps-v||_E <= (M+D) eps^(1/2) + C eps^(3/2)
 ||g_eps-g||_{L^q_t L^p_x}
   <= C_{p,q} (eps^alpha + eps^(alpha+1))
```

and specifies positive-time force norms and
`alpha(p,q)=-3+3/p+2/q` at `paper/sections/03-torus.tex:308-309`.  The upstream
packet equalities are exactly the two `eps^(1/2)` identities at
`paper/sections/03-torus.tex:125-131`, and the correction rates are exactly
`eps^(3/2)` and `eps^(alpha+1)` at
`paper/sections/03-torus.tex:232-242`.  The insertion identities used by the
proof are stated at `paper/sections/03-torus.tex:313-318`.

## 2. What is in Lean

### Statement fidelity

The five requested fields match the reconciled Spec.

- `energyRate` is at
  `formalization/NSFormalization/Section3/T18/EnergyRate.lean:262`.  Its two
  premises are precisely `0 <= data.energyBound` and
  `0 <= data.dissipationBound`; its conclusion at lines 264-267 is the Spec
  conclusion at `research/T18/Spec.lean:1892-1895` under the U1 projections.
  They are honest, load-bearing premises: the proof uses them in both
  `ENNReal.ofReal_add` rewrites at
  `formalization/NSFormalization/Section3/T18/EnergyRate.lean:273-277`.
- `forceDiffMixedConst`, `_nonneg`, `forceDifference_mixed_memLp`, and
  `forceDifference_mixed_bound` occur at
  `formalization/NSFormalization/Section3/T18/MixedRate.lean:146`, `:154`,
  `:163`, and `:186`.  Their quantifier order and conclusions match
  `research/T18/Spec.lean:1899-1924`.  The local `alphaT` is the paper formula
  (`formalization/NSFormalization/Section3/T15/Bridges.lean:78-80`) and the
  probe unfolds it together with the copied contract formula
  (`research/T18/probes/u9_u10_closes.lean:206-214`).
- The fieldwise conformance constructor calls canonical `energyRate` directly
  at `research/T18/probes/u9_u10_closes.lean:202-205`.  Its sign proofs use the
  actual `PacketAPI.energy_isLUB` and `dissipation_eq` clauses at
  `verification/Contracts/V1/Packet.lean:248-267`; the derived lemmas are at
  `research/T18/probes/u9_u10_closes.lean:160-172`.

There is no vacuity from an empty scale interval: `epsilon0` is a minimum and
`eps_pos` proves it positive at
`formalization/NSFormalization/Section3/T18/Insertion.lean:98-103`.  The review
probe gives the explicit inhabitant `epsilon0 data` at
`research/T18/probes/rev443_nonvacuity.lean:15-16` and typechecks with zero
output.

The energy norm is the actual `essSup + gradient lintegral` quantity
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:327-341`).  Its
slice guards and exact packet identities are the record fields at
`formalization/NSFormalization/Section3/T15/Scaling.lean:333-366`; the
correction guards and rate are at
`formalization/NSFormalization/Section3/T17/Correction.lean:220-241`.

The mixed result is also non-vacuous.  `MemMixedLebesgueT` contains an actual
slice path and `MemLp` proof
(`formalization/NSFormalization/Section3/T15/Scaling.lean:79-84`).  The lane
derives the correction witness from strict finiteness at
`formalization/NSFormalization/Section3/T18/MixedRate.lean:56-76` and
`:122-132`, and takes the packet witness from `ScalingAPI.mixed_memLp`, whose
honesty contract is at
`formalization/NSFormalization/Section3/T15/Scaling.lean:368-394`.  No theorem
has an unused named hypothesis that weakens the requested result.

### Hygiene and axiom surface

`git diff --name-status origin/erenup/integration-section3...HEAD` reports:

```text
A formalization/NSFormalization/Section3/T18/EnergyRate.lean
A formalization/NSFormalization/Section3/T18/MixedRate.lean
A research/T18/ATTEMPTS_U9_U10.md
A research/T18/REPORT_443.md
M research/T18/T18_SPLIT.md
A research/T18/axioms_u9_u10.lean
A research/T18/probes/u9_u10_closes.lean
```

Thus both Lean implementation modules are new; no existing Lean module or
`verification/` file was modified.  The implementation/conformance scan for
`sorry`, `admit`, declaration-form `axiom`, and `native_decide` is empty.  The
`set_option maxHeartbeats` scan is also empty.  `git diff --check
origin/erenup/integration-section3...HEAD` has zero output and exit 0.

The audit file contains 24 `#print axioms` commands
(`research/T18/axioms_u9_u10.lean:13-37`).  Its exact result is the standard
list in every case:

```text
energyTorusChart                              [propext, Classical.choice, Quot.sound]
contDiffOn_spatialFDeriv                      [propext, Classical.choice, Quot.sound]
spatialGradient_add                           [propext, Classical.choice, Quot.sound]
gradientSliceNorm_aemeasurable                [propext, Classical.choice, Quot.sound]
energyEssSupT_add_le                          [propext, Classical.choice, Quot.sound]
energyGradientT_add_le                        [propext, Classical.choice, Quot.sound]
energyENormT_add_le                           [propext, Classical.choice, Quot.sound]
velocityDifference_eq_correction_add_packet  [propext, Classical.choice, Quot.sound]
velocityDifference_energyENorm_le             [propext, Classical.choice, Quot.sound]
packet_energyENorm_eq                         [propext, Classical.choice, Quot.sound]
energyRate_separateConstants                  [propext, Classical.choice, Quot.sound]
energyRate                                    [propext, Classical.choice, Quot.sound]
mixedLebesgueENormT_eq_of_path                [propext, Classical.choice, Quot.sound]
mixedLebesgueENorm_eq_of_path                 [propext, Classical.choice, Quot.sound]
memMixedLebesgueT_of_lt_top                   [propext, Classical.choice, Quot.sound]
periodicLebesgueSlicePath_add                 [propext, Classical.choice, Quot.sound]
memMixedLebesgueT_add                         [propext, Classical.choice, Quot.sound]
mixedLebesgueENormT_add_le                    [propext, Classical.choice, Quot.sound]
correctionForce_mixed_memLp                   [propext, Classical.choice, Quot.sound]
packetSource_mixedNorm_ne_top                 [propext, Classical.choice, Quot.sound]
forceDiffMixedConst                           [propext, Classical.choice, Quot.sound]
forceDiffMixedConst_nonneg                    [propext, Classical.choice, Quot.sound]
forceDifference_mixed_memLp                   [propext, Classical.choice, Quot.sound]
forceDifference_mixed_bound                   [propext, Classical.choice, Quot.sound]
```

### Negative mutation

`research/T18/probes/rev443_mutation.lean:16-25` substantively widens the main
theorem's interval from `(0, epsilon0]` to `(-1, epsilon0]`; it does not merely
drop an argument.  The attempted canonical proof fails exactly because the
positive-scale guard is load-bearing:

```text
Mutation exit=1
../research/T18/probes/rev443_mutation.lean:25:32: error: Application type mismatch: The argument
  hε
has type
  ε ∈ Ioc (-1) (ε₀ data)
but is expected to have type
  ε ∈ Ioc 0 (ε₀ data)
in the application
  energyRate data hM hD ε hε
```

## 3. Gaps

There is no current U9 or U10 gap.  The report's original U9 residual is
historical and explicitly superseded by the continuation ruling.  The two raw
sign premises are appropriate at the canonical boundary because
`InsertionData` stores only the real constants and `ScalingAPI`, not the
packet clauses (`formalization/NSFormalization/Section3/T18/Insertion.lean:37-57`).
The Spec-boundary probe supplies those clauses and closes the exact field.

For completeness, the required whole-Section4 search was run:

```text
$ grep -rnE "energyBound_nonneg|dissipationBound_nonneg|0 ≤ .*energyBound|0 ≤ .*dissipationBound|energyRate" formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/I03/Energy.lean:123:theorem energyBound_nonneg (hP : PacketData U K M D) : 0 ≤ M := by
formalization/NSFormalization/Section4/I03/Energy.lean:154:    simpa [this] using energyBound_nonneg hP
```

This is not a counterexample to the interface analysis: the found theorem
requires `PacketData`, which canonical `InsertionData` does not retain.  No
current report gap or other “not in the tree” claim remains.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

1. Required module build:

   ```text
   $ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.EnergyRate NSFormalization.Section3.T18.MixedRate
   Build completed successfully (10021 jobs).
   EXIT=0
   ```

   Before that exact terminal line, Lake replayed pre-existing dependency
   linter warnings; none named `EnergyRate` or `MixedRate`, and there was no
   error.

2. Direct checks and conformance/non-vacuity probes produced exactly zero Lean
   output:

   ```text
   EnergyRate exit=0 bytes=0
   MixedRate exit=0 bytes=0
   Conformance exit=0 bytes=0
   Nonvacuity exit=0 bytes=0
   ```

   These correspond respectively to:

   ```text
   lake env lean ../formalization/NSFormalization/Section3/T18/EnergyRate.lean
   lake env lean ../formalization/NSFormalization/Section3/T18/MixedRate.lean
   lake env lean ../research/T18/probes/u9_u10_closes.lean
   lake env lean ../research/T18/probes/rev443_nonvacuity.lean
   ```

3. Axiom audit:

   ```text
   $ lake env lean ../research/T18/axioms_u9_u10.lean
   EXIT=0
   #print commands=24
   all 24 lists=[propext, Classical.choice, Quot.sound]
   ```

   The per-declaration exact lists are pasted in section 2 above.  Lean wrapped
   two long declaration names across lines but printed the same three-element
   list and no other axiom.

4. Root gate:

   ```text
   $ make check
   EXIT=0
   output bytes=2170111 lines=52503
   SHA256=77d0bb1e29cddb1cb709959bb3a4a482c3c96da9e7f14fc68a7548dfef053493
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.046s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The large middle block is the exact contract-closure JSON; its final object
   reports `"base_compatibility_checked": false` because this was ordinary
   `make check`, not the conditional base-ref command.

5. `scripts/gates.sh` and
   `check_contracts.py --base-ref origin/erenup/integration-section3` were not
   applicable: the base diff contains no path under `verification/`.  Ordinary
   `make check` did run `experiments/check_contracts.py` successfully.

No fixes required.
