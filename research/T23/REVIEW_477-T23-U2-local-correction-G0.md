REJECT

## 1. What the lane claims

The worker accurately labels this a **partial** delivery, not a completed U2
supplier (`research/T23/REPORT_477.md:1`, `research/T23/REPORT_477.md:50-68`).
The report makes three positive Lean claims:

1. The literal G0 API has no inhabitant when the supplied cutoff has
   `D.ε₀ = 0`, and a repaired statement existentially chooses matching correction
   and cutoff data (`research/T23/REPORT_477.md:8-14`).
2. A single raw `D` is constructed with cutoff, radial-potential, cancellation,
   support, smoothness, cross-transport, force-support, and derivative-jet
   properties (`research/T23/REPORT_477.md:15-21`).
3. A spatially and temporally truncated solenoidal extension transfers the
   correction and force to a globally smooth reference (`research/T23/REPORT_477.md:22-27`).

Those claims are honest and match the declarations that actually exist. The
rejection is because the brief asked for the complete canonical G0 deliverable
and the complete local correction supplier, whereas the report itself records
that both remain unfinished.

Statement-fidelity checks:

- The standalone probe contains `research/T23/Spec.lean` byte-for-byte after its
  two-line preamble: `diff -u research/T23/Spec.lean <(sed -n '3,1085p'
  research/T23/probes/g0_counterexample.lean)` produced no output. The literal
  statement is at `research/T23/probes/g0_counterexample.lean:1039-1050`, the
  zero-cutoff theorem at `research/T23/probes/g0_counterexample.lean:1092-1104`,
  and the repaired definition at
  `research/T23/probes/g0_counterexample.lean:1106-1126`. The repaired definition
  really adds `0 < r`, both ball inclusions, and existentially matching `C,D`.
- The seven raw `CutoffData` fields at
  `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:16-56` are
  byte-for-byte the structure block at `research/T23/Spec.lean:130-170`; the
  direct `diff` produced no output.
- The two cross transports at
  `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:296-303`
  retain the un-periodised packet and `Ico 0 T`, matching
  `research/T23/Spec.lean:879-891` and the open-neighbourhood proof pattern at
  `formalization/NSFormalization/Section3/T18/CrossTransport.lean:46-79`.
- The core constructor exists with the claimed hypotheses and conclusion at
  `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:308-360`.
  The force/jet constructor exists at
  `formalization/NSFormalization/Section3/T23/LocalCorrectionBridge.lean:117-167`.
  The spatial/window extensions and global correction/force equality are at
  `formalization/NSFormalization/Section3/T23/SpatialExtension.lean:16-43`,
  `formalization/NSFormalization/Section3/T23/SpatialExtension.lean:47-78`, and
  `formalization/NSFormalization/Section3/T23/LocalCorrectionBridge.lean:17-74`.
- These statements cover the local potential, cutoff, support, cancellation,
  and pointwise derivative bounds in the paper
  (`paper/sections/03-torus.tex:167-215`,
  `paper/sections/03-torus.tex:218-242`). They do not cover all of the latter
  block's energy, mixed-Lebesgue, and Sobolev conclusions
  (`paper/sections/03-torus.tex:232-242`).
- No hidden empty scale interval is used: `LocalCorrectionCore.eps_pos` is a
  field at `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:270`,
  and the review probe constructs the concrete zero-field instance together
  with `D.ε₀ ∈ Ioc 0 D.ε₀` at
  `research/T23/probes/rev477_statement_checks.lean:10-27`. The domain inclusion
  hypothesis is used in the support conclusion at
  `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:469`; the
  positivity and compactness hypotheses feed the actual cutoff/threshold
  constructors at `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:316-354`.
  I found no `⊤.toReal = 0`, empty-interval argument, conclusion-shaped input,
  or unused mathematical binder making a claimed result vacuous.

## 2. What is in Lean

The following substantial partial result is kernel checked:

- `LocalCorrectionCore` records smooth cutoffs, a positive common threshold,
  the radial potential/curl identity, a globally smooth compact solenoidal
  correction, support, open-neighbourhood cancellation, and both cross
  transports (`formalization/NSFormalization/Section3/T23/LocalCorrection.lean:255-303`).
- `exists_localCorrection_in_domain` additionally proves force smoothness,
  compactness, and domain/interior support
  (`formalization/NSFormalization/Section3/T23/LocalCorrection.lean:443-470`).
- `exists_localCorrection_with_derivative_bounds` retains the same actual `D`
  while adding correction and force jet bounds with constants chosen before
  `ε` (`formalization/NSFormalization/Section3/T23/LocalCorrectionBridge.lean:117-167`).
- The endpoint argument is real: the inactive packet slice is proved at
  `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:61-72`, and the
  `t = 0` branch is consumed at
  `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:229-245`.
- The canonical `StatementRepair` module, however, contains only `zeroCutoff`
  and `zeroCutoff_no_positive_threshold`
  (`formalization/NSFormalization/Section3/T23/StatementRepair.lean:9-18`).

The substantive mutation widens the required cross-transport time interval from
`Ico 0 T` to `Icc 0 T`. Reusing the theorem fails, as guarded at
`research/T23/probes/rev477_statement_checks.lean:29-56`, with exactly:

```text
error: Type mismatch
  h.crossTransport_background_advects_packet
has type
  ∀ ε ∈ Ioc 0 D.ε₀,
    ∀ t ∈ Ico 0 T,
      ∀ (x : Space),
        (spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) t x)
            (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) =
          0
but is expected to have type
  ∀ ε ∈ Ioc 0 D.ε₀,
    ∀ t ∈ Icc 0 T,
      ∀ (x : Space),
        (spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) t x)
            (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) =
          0
```

All 21 declarations listed in `research/T23/axioms_u2.lean:5-25` print exactly
`[propext, Classical.choice, Quot.sound]`; the G0 theorem's guarded audit is at
`research/T23/probes/g0_counterexample.lean:1130-1132`.

Hygiene is otherwise sound:

- all four implementation modules are additions, not modifications; the only
  modified tracked files are the two research records
  `research/T23/SPEC_ISSUES.md` and `research/T23/T23_SPLIT.md`;
- no `maxHeartbeats` occurs;
- no implementation module contains `sorry`, `admit`, `axiom`, or
  `native_decide`; the standalone verbatim Spec probe has three comment-only
  occurrences of the word `sorry` at
  `research/T23/probes/g0_counterexample.lean:20`, `:95`, and `:543`, but no
  admission or axiom declaration;
- no direct or transitive local-source import of `Paper1/BoundaryCorollary` was
  found (647 local source files traversed, zero matching import edges);
- no file under `verification/` was touched, so the conditional
  `scripts/gates.sh` and base-ref contract gate do not apply.

## 3. Gaps and required fixes

1. **Blocking: the canonical G0 deliverable is absent.** The brief required
   `StatementRepair.lean` to contain the literal statement, its exact
   counterexample, and `boundaryInsertionStatement'`. Instead those declarations
   exist only in the research probe, exactly as the worker acknowledges at
   `research/T23/REPORT_477.md:54-59`. The reproducer guarded at
   `research/T23/probes/rev477_statement_checks.lean:58-63` is:

   ```text
   error: Unknown identifier `NSFormalization.Section3.T23.boundaryInsertionStatement'`
   ```

   **Fix:** put the literal API-facing statement, `boundaryInsertionAPI_zero_cutoff`,
   and the repaired existential statement in the required canonical module (or
   first land/import the canonical domain vocabulary needed to state them there),
   then add them to the axiom audit.

2. **Blocking: the requested local supplier is incomplete.** The delivered final
   theorem stops at smoothness/support and pointwise jet bounds
   (`formalization/NSFormalization/Section3/T23/LocalCorrectionBridge.lean:127-142`).
   It neither constructs/consumes the matching registered I02/I03 pair nor proves
   correction energy, mixed-Lebesgue, and Sobolev-force estimates at that same
   `D`; the worker explicitly records these residuals at
   `research/T23/REPORT_477.md:60-68` and
   `research/T23/ATTEMPTS_U2.md:82-127`. These are mathematical conclusions of
   the cited paper block (`paper/sections/03-torus.tex:232-242`), not optional
   packaging.

   **Fix:** construct and retain a matching `CorrectionAPI`/`ScalingAPI` pair
   with `A.correction = C`, transport the energy/mixed/Sobolev estimates through
   the proved global correction/force equalities, and expose one constructor at
   the same chosen `D` and threshold. Update `local_correction_closes.lean` to
   exercise that full statement.

3. **The gaps are not concealed by a missed Section 4 declaration.** Required
   whole-tree searches were run. There is no Section 4 definition of
   `BoundaryInsertionAPI`, `boundaryInsertionStatement`, or
   `ClassicalSolutionOmega`, and no theorem named `correction_energy_bound`,
   `force_mixed_bound`, or `force_sobolev_bound`. Section 4 does contain generic
   analytic ingredients such as `energyEssSup_le` and `energyGradient_le`
   (`formalization/NSFormalization/Section4/I02/Energy.lean:103-158`) and
   `exists_slicePath` (`formalization/NSFormalization/Section4/I02/Mixed.lean:104-120`),
   so the remaining issue is the same-`D` local-to-registered transfer, not an
   honest claim that no analytic infrastructure exists.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`; every `lake` invocation ran
from `verification/` with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section3.T23.StatementRepair NSFormalization.Section3.T23.LocalCorrection
⚠ [8778/9154] Replayed NSFormalization.Source.FiniteHilbertBochner
⚠ [9838/9906] Replayed NSFormalization.Source.RealSobolev
⚠ [9842/9906] Replayed NSFormalization.Paper3.SpatiallyCompactTime
⚠ [9849/9906] Replayed NSFormalization.Paper3.RealPositiveDensity
⚠ [9852/9906] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
⚠ [9862/9906] Replayed NSFormalization.Source.PacketForceExtension
⚠ [9865/9906] Replayed NSFormalization.Source.ViscosityPacket
ℹ [9882/9906] Replayed NSFormalization.Source.PhysicalBesselSobolev
⚠ [9899/9906] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
Build completed successfully (9906 jobs).

$ lake build NSFormalization.Section3.T23.StatementRepair NSFormalization.Section3.T23.LocalCorrection NSFormalization.Section3.T23.LocalCorrectionBridge
⚠ [8778/8858] Replayed NSFormalization.Source.FiniteHilbertBochner
⚠ [9838/9908] Replayed NSFormalization.Source.RealSobolev
⚠ [9842/9908] Replayed NSFormalization.Paper3.SpatiallyCompactTime
⚠ [9849/9908] Replayed NSFormalization.Paper3.RealPositiveDensity
⚠ [9852/9908] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
⚠ [9862/9908] Replayed NSFormalization.Source.PacketForceExtension
⚠ [9865/9908] Replayed NSFormalization.Source.ViscosityPacket
ℹ [9882/9908] Replayed NSFormalization.Source.PhysicalBesselSobolev
⚠ [9899/9908] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
Build completed successfully (9908 jobs).
```

The replayed diagnostics are all from the named upstream files; neither T23
module emitted a diagnostic.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T23/StatementRepair.lean
[no output; exit 0]
$ lake env lean ../formalization/NSFormalization/Section3/T23/LocalCorrection.lean
[no output; exit 0]
$ lake env lean ../formalization/NSFormalization/Section3/T23/SpatialExtension.lean
[no output; exit 0]
$ lake env lean ../formalization/NSFormalization/Section3/T23/LocalCorrectionBridge.lean
[no output; exit 0]
$ lake env lean ../research/T23/probes/g0_counterexample.lean
[no output; exit 0]
$ lake env lean ../research/T23/probes/local_correction_closes.lean
[no output; exit 0]
$ lake env lean ../research/T23/probes/rev477_statement_checks.lean
[no output; exit 0]
```

Exact axiom output:

```text
'NSFormalization.Section3.T23.packet_slice_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.physicalCorrection_cancels_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.crossTransport_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.exists_localCorrectionCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.correctionForce_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.force_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.correctionForce_eq_of_open_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.force_smooth_of_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.correction_support_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.exists_localCorrection_in_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.LocalCorrectionCore.correction_eq_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.LocalCorrectionCore.threshold_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.correction_support_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.force_support_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.zeroCutoff_no_positive_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.exists_spatial_solenoidal_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.exists_solenoidal_window_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.physicalCorrection_eq_of_cylinder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.exists_matching_global_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.exists_local_derivative_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.exists_localCorrection_with_derivative_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`make check` was run twice and exited 0. The second run filtered the enormous
architecture JSON only for stable result lines; its exact displayed output was:

```text
python3 experiments/check_formalization_plan.py --check
  "source_hashes_match": false
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
  "base_compatibility_checked": false,
python3 experiments/test_contract_policy.py
.............
Ran 13 tests in 0.043s
OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The broad inventory's `source_hashes_match: false` and copied-source admission
count are pre-existing repository-wide results; the lane declaration audits above
remain standard.

Required absence searches:

```text
$ grep -rnE 'structure BoundaryInsertionAPI|def boundaryInsertionStatement|structure ClassicalSolutionOmega' --include='*.lean' formalization/NSFormalization/Section4
[no output; exit 1]
$ grep -rnE 'A\.correction = C|CorrectionAPI.*ScalingAPI|ScalingAPI.*CorrectionAPI|matching.*correction' --include='*.lean' formalization/NSFormalization/Section4
[no output; exit 1]
$ grep -rnE 'theorem (correction_energy_bound|force_mixed_bound|force_sobolev_bound)' --include='*.lean' formalization/NSFormalization/Section4
[no output; exit 1]
```

Repository hygiene/status output:

```text
$ git diff --diff-filter=M --name-status origin/erenup/integration-section3...HEAD
M	research/T23/SPEC_ISSUES.md
M	research/T23/T23_SPLIT.md
$ git diff --diff-filter=A --name-status origin/erenup/integration-section3...HEAD
A	formalization/NSFormalization/Section3/T23/LocalCorrection.lean
A	formalization/NSFormalization/Section3/T23/LocalCorrectionBridge.lean
A	formalization/NSFormalization/Section3/T23/SpatialExtension.lean
A	formalization/NSFormalization/Section3/T23/StatementRepair.lean
A	research/T23/ATTEMPTS_U2.md
A	research/T23/REPORT_477.md
A	research/T23/axioms_u2.lean
A	research/T23/axioms_u2.log
A	research/T23/probes/g0_counterexample.lean
A	research/T23/probes/local_correction_closes.lean
$ git diff --check origin/erenup/integration-section3...HEAD
[no output; exit 0]
$ git diff --name-only origin/erenup/integration-section3...HEAD -- verification/
[no output; exit 0]
```

Because `verification/` is untouched, `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` were not run;
they are conditional in the review instructions.

## Lead ruling (2026-09-19 16:40Z)
The REJECT is recorded as correct against the brief's full deliverable list; the mathematics delivered is honest (all gates and axioms pass) and the brief explicitly allowed an honest partial. Lead decision: **merge the partial** as U2 stage 1. Fix 1 (canonical literal/repaired G0 statements in the implementation tree) is already assigned to lane 480 (T23 U-CAN, running on this branch); fixes 2–3 (matching registered I02/I03 supplier at the same `D` with `A.correction = C`; energy / mixed-Lebesgue / Sobolev-force estimates; complete `local_correction_closes.lean`) become lane U2b (481) on top of 480. No claim of a complete U2 is made anywhere in the tree (`T23_SPLIT.md` status stays "partial").
