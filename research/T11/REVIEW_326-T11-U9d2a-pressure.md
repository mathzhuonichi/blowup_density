REJECT

## 1. What the lane claims

The worker reports a genuine partial delivery: a coefficient formula, scalar
Fourier inversion, periodicity, gauge, spatial slice smoothness,
`pressure_gradient`, and the pressure Poisson equation, while explicitly leaving
joint slab smoothness open (`research/T11/REPORT_326.md:9-25`,
`research/T11/REPORT_326.md:96-120`).  That is the right mathematical pressure
prescription: the paper requires
`Delta p = div f - div (div (u tensor u))` with zero mean
(`paper/sections/02-preliminaries.tex:84-88`), and the canonical Lean fields are
joint `pressure_smooth`, gradient `MemLp`, periodicity, and gauge
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:275-299`) plus the
same pointwise Poisson equation
(`formalization/NSFormalization/Section3/T11/LocalTheory.lean:78-88`).

The report also claims that `mildPressure_gradient_leray_complement` says the
gradient has datum `(I-P)(F-Q)`, and that
`mildPressureSourceCoeff_eq_force_sub_convection` identifies the source with
canonical coefficient data `F-Q` (`research/T11/REPORT_326.md:45-60`).  This
second claim is stronger than the Lean statement; it is the main fidelity
failure below.

The report's declaration count is accurate: the module has 78 top-level
`def`/`theorem`/`structure` declarations and two explicitly named local
instances (`formalization/NSFormalization/Section3/T11/MildPressure.lean:23-26`).

## 2. What is in Lean

The substantial positive content is present and matches the statements claimed:

- `lerayPotentialCoeff` is genuinely constructed, with zero mode `0` and the
  nonzero-mode quotient by `2*pi*i*sum k_j^2`
  (`formalization/NSFormalization/Section3/T11/MildPressure.lean:157-165`).  Its
  derivative-symbol/Leray-complement identity has the honestly exposed
  hypotheses `hB : IsPeriodicDatum s S B` and `k != 0`
  (`formalization/NSFormalization/Section3/T11/MildPressure.lean:267-292`).  This
  agrees with the canonical derivative and Leray symbols
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:184-202`).
- `mildPressureCoeff` and `mildPressure` are actual source-to-coefficient and
  Fourier-inversion constructions, not aliases of an assumed pressure
  (`formalization/NSFormalization/Section3/T11/MildPressure.lean:619-652`).
- Spatial smoothness, periodicity, gauge, and gradient `MemLp` have the reported
  statements
  (`formalization/NSFormalization/Section3/T11/MildPressure.lean:658-689`).
  `mildPressure_poisson` has exactly the `PeriodicLocalRegularity` field shape
  (`formalization/NSFormalization/Section3/T11/MildPressure.lean:699-738`).
- `MildPressureFields` bundles precisely the delivered spatial/periodic/gauge/
  gradient/Poisson results and is constructed from force smoothness, force
  periodicity, and `PersistenceInput T u`; it does not package a target as an
  input (`formalization/NSFormalization/Section3/T11/MildPressure.lean:813-844`).
- The non-vacuity theorem uses `T = 1`, a genuine `PersistenceInput`, and proves
  a nonzero pressure slice
  (`formalization/NSFormalization/Section3/T11/MildPressure.lean:994-1007`).
  Thus the delivered hypotheses are not certified only through an empty
  interval.  It does not, however, include a `TorusForcedMildOn` witness for
  that particular force/path, so it is non-vacuity of the pressure package, not
  of all U9d hypotheses.

The theorem statements named in the report are therefore real and accurately
described except for the canonical `F-Q` identification discussed next.  Joint
`pressure_smooth` is genuinely absent, as the report admits: `PersistenceInput`
only supplies `ContinuousOn` coefficient paths
(`formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean:25-30`).

## 3. Gaps and blocking findings

1. **High — the reported canonical `F-Q` coefficient identity is not proved.**
   The actual conclusion of `mildPressureSourceCoeff_eq_force_sub_convection`
   leaves the nonlinear term as
   `periodicFourierCoeff (convectionDivergenceT (torusPhysicalVelocity u) ...)`
   (`formalization/NSFormalization/Section3/T11/MildPressure.lean:779-811`).  It
   does not identify that coefficient with the canonical unprojected
   `torusConvectionDatum (u t) (u t)`, defined and characterized at
   `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:272-284`.
   Likewise, `mildPressure_gradient_leray_complement` accepts an arbitrary
   already-supplied datum `B` of the physical source
   (`formalization/NSFormalization/Section3/T11/MildPressure.lean:757-770`);
   it does not construct `B = F-Q`.

   Reproducer: `research/T11/probes/rev326_canonical_q_gap.lean:13-19` asks for
   the report's canonical coefficient-side conclusion. Exact compiler output:

   ```text
   ../research/T11/probes/rev326_canonical_q_gap.lean:19:2: error: Type mismatch
     mildPressureSourceCoeff_eq_force_sub_convection hu hF ht j k
   has type
     sourceComponentCoeff (fun x => mildPressureSource g u (t, x)) j k =
       torusPhysicalCoeff 3 (F t) j k -
         periodicFourierCoeff (fun x => ↑((convectionDivergenceT (torusPhysicalVelocity u) t x).ofLp j)) k
   but is expected to have type
     sourceComponentCoeff (fun x => mildPressureSource g u (t, x)) j k =
       torusPhysicalCoeff 3 (F t) j k - torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k
   ```

   Fix: either prove the physical-product Fourier/convolution bridge and then
   export the exact canonical `F-Q` theorem, or change every report/status claim
   to say that this bridge is an additional exact residual.  A partial delivery
   is allowed, but its gap list must be complete.

2. **Medium — the all-orders coefficient Sobolev deliverable is not exported or
   listed as a gap.**  The brief asks for the pressure coefficient in every
   `H^m`.  The module proves the stronger-looking weighted absolute summability
   estimate for the raw coefficient family
   (`formalization/NSFormalization/Section3/T11/MildPressure.lean:304-322`), but
   it never packages the order-`m` weighted coefficient as the relevant scalar
   Sobolev datum or states the requested membership theorem.  Neither
   `research/T11/REPORT_326.md:96-123` nor the U9d2a status calls this out.

   Fix: add the all-order datum/membership theorem, or record its exact statement
   as a second residual in the report, attempts file, split row, and route status.

3. **Blocking gate — two `#print axioms` results are not exactly the required
   three-element list.**  The guarded audit itself declares the exceptions
   (`research/T11/axioms_mild_pressure.lean:3-6`, and specifically lines 288 and
   296).  The reviewer probe `research/T11/probes/rev326_axiom_exact.lean:1-5`
   printed:

   ```text
   'NSFormalization.Section3.T11.mildPressure_fields' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.testFrequency' depends on axioms: [propext]
   'NSFormalization.Section3.T11.testFrequency_ne_neg' depends on axioms: [propext]
   ```

   This is not an unsoundness issue—the two outputs are strict subsets—but it
   fails the review instruction that every printed result be exactly
   `[propext, Classical.choice, Quot.sound]`.  Fix the audit/declarations to meet
   the stated exact gate, or obtain an explicit relaxation from the lead.

4. **Disclosed and acceptable for a partial lane:** joint slab
   `pressure_smooth` is not proved; even joint continuity is absent
   (`research/T11/REPORT_326.md:98-116`).  This prevents assembly of all
   `ClassicalSolutionT` pressure fields but is honestly isolated.  The report's
   stronger sentence that the *one* residual is joint smoothness must be revised
   because findings 1 and 2 are separate coefficient-side deliverables.

5. **The “not in the tree” claim was checked and is supported.**  Literal
   `grep -rn` over the whole `formalization/NSFormalization/Section4` tree and
   the broader required roots found no theorem identifying the Fourier
   coefficient of a smooth periodic product with the infinite convolution.
   The nearest hit is only a finite-support algebraic coefficient definition
   (`formalization/NSFormalization/Paper1/PeriodicPicardBilinear.lean:9-16`),
   explicitly documented as having no PDE claim.  Thus the missing bridge
   described at `research/T11/ATTEMPTS_MILD_PRESSURE.md:78-80` really is absent.

Hygiene otherwise passes. The only formalization file in the branch diff is a
new module; no existing Lean module was modified. There are no source matches
for `sorry`, `admit`, `axiom`, or `native_decide`; the sole heartbeat override is
per declaration, exactly `400000`, and has a preceding explanation
(`formalization/NSFormalization/Section3/T11/MildPressure.lean:126-131`). The two
local instances are explicitly named
(`formalization/NSFormalization/Section3/T11/MildPressure.lean:23-26`).

The substantive negative mutation changes the Poisson nonlinear sign from
subtraction to addition (`research/T11/probes/rev326_pressure_sign_mutation.lean:13-21`).
It fails for the expected reason, not because an argument was removed:

```text
../research/T11/probes/rev326_pressure_sign_mutation.lean:21:2: error: Type mismatch
  mildPressure_poisson hg hgp hu
has type
  ∀ t ∈ Ico 0 T,
    ∀ (x : Space),
      scalarSpatialLaplacianT (mildPressure g u) t x =
        spatialDivergence g t x -
          spatialDivergence (fun z => convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x
but is expected to have type
  ∀ t ∈ Ico 0 T,
    ∀ (x : Space),
      scalarSpatialLaplacianT (mildPressure g u) t x =
        spatialDivergence g t x +
          spatialDivergence (fun z => convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x
```

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; every `lake` command
was run from `verification/` with `LEAN_NUM_THREADS=6` for the build.

1. `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildPressure`
   exited 0. It replayed warnings from dependencies, but none from
   `MildPressure.lean`. Exact beginning/end excerpts (the omitted middle is only
   replayed dependency diagnostics):

   ```text
   ⚠ [8778/9095] Replayed NSFormalization.Source.FiniteHilbertBochner
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

   Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
     PiLp.single_apply
   ...
   warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.

   Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
     [apply] _hS

   Note: This linter can be disabled with `set_option linter.unusedVariables false`
   Build completed successfully (9986 jobs).
   ```

2. These three commands each exited 0 with exactly zero output:

   ```text
   lake env lean ../formalization/NSFormalization/Section3/T11/MildPressure.lean
   <empty>
   lake env lean ../research/T11/probes/mild_pressure_closes.lean
   <empty>
   lake env lean ../research/T11/axioms_mild_pressure.lean
   <empty>
   ```

   The last is silent because its prints are wrapped in `#guard_msgs`; the
   unguarded reviewer output exposing the two strict-subset exceptions is quoted
   in finding 3.

3. `make check` exited 0. Its contract-closure JSON is very large; exact head
   and tail are:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
     "source_counts": {
       "formalization": 574,
       "vendor/NavierStokesAndEuler": 2486,
       "vendor/HeliCorgi": 129
     },
     "source_manifest_entries": 2975,
     "missing_copied_imports": [],
     "citation_interfaces_reachable": [],
   ...
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.047s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

4. `git diff --name-status origin/erenup/integration-section3...HEAD` produced:

   ```text
   A formalization/NSFormalization/Section3/T11/MildPressure.lean
   A research/T11/ATTEMPTS_MILD_PRESSURE.md
   M research/T11/EXISTENCE_ROUTE.md
   A research/T11/REPORT_326.md
   M research/T11/T11_SPLIT.md
   A research/T11/axioms_mild_pressure.lean
   A research/T11/probes/mild_pressure_closes.lean
   ```

   Therefore no `verification/` file was touched. Per the review instruction,
   `scripts/gates.sh` and
   `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
   were not applicable and were not run. `make check` did run the ordinary
   `check_contracts.py` successfully, as shown above.

Required fixes before acceptance:

1. Prove the exact physical-Fourier/canonical-convolution bridge needed for
   `torusConvectionDatum`, or list that exact theorem as an unproved residual and
   remove the canonical `(I-P)(F-Q)` overclaim everywhere.
2. Export the promised every-`H^m` coefficient-pressure membership/datum theorem,
   or list its exact statement as an additional residual in all status records.
3. Make every audited `#print axioms` output exactly the mandated three axioms,
   or obtain an explicit change to that gate.
