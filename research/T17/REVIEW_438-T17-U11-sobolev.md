ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims all four U11 outputs at the concrete `correctionData`: an
explicit real function `sobolevConst`, strict positivity on `0 ≤ s ≤ 1`, an honest
`MemForceSobolevT 1 s` path, and

```
forceSobolevENormT 1 s (correctionForce … ε) ≤
  ENNReal.ofReal (C s * (ε^(3/2) + ε^(3/2-s))).
```

That is the paper's `eq:HHs`: the displayed range, exponent, sum of the
inhomogeneous and homogeneous rates, and independence of the constant from
small `ε` occur at `paper/sections/03-torus.tex:238-242`; the proof explains the
two rates and localization at `paper/sections/03-torus.tex:275-284`.  The worker
also explicitly says that it uses periodic Fourier interpolation rather than
the planned T13-localization proof (`research/T17/REPORT_438.md:53`).

The report accurately exposes the two assumptions not present as binders in the
raw record fields: global smoothness `hv` and the normalization `ε₀ ≤ 1`
(`research/T17/REPORT_438.md:11-21`, `research/T17/REPORT_438.md:76`).  They are
ordinary, isolated hypotheses, not named `Prop` inputs or repackaged goals.

## 2. What is in Lean

### Statement fidelity

The canonical fields are exactly:

- `sobolevConst : ℝ → ℝ` and strict positivity on `[0,1]` at
  `formalization/NSFormalization/Section3/T17/Correction.lean:262-268`;
- the honest path at
  `formalization/NSFormalization/Section3/T17/Correction.lean:269-273`;
- the bound, including `Ioc 0 D.ε₀`, `3/2-s`, and the sum of both powers, at
  `formalization/NSFormalization/Section3/T17/Correction.lean:274-281`.

The delivered constant is defined before `ε` and is
`1 + ∑ i, c₀(i)^(1-s) (2πc₁(i))^s` at
`formalization/NSFormalization/Section3/T17/Sobolev.lean:273-280`.  Its endpoint
constants are finite by the selected Paper1 statement
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:257-271` and
`formalization/NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:20-44`).
The added `1` makes the constant strictly positive; no `ENNReal.toReal ⊤ = 0`
collapse is used (`formalization/NSFormalization/Section3/T17/Sobolev.lean:282-304`).

The two public theorem conclusions are literal concrete-data instances of the
canonical fields:

- `forceSobolev_memLp` at
  `formalization/NSFormalization/Section3/T17/Sobolev.lean:546-565`;
- `force_sobolev_bound` at
  `formalization/NSFormalization/Section3/T17/Sobolev.lean:567-590`.

The conformance probe repeats those types and closes them by `exact` at
`research/T17/probes/sobolev_closes.lean:37-84`; the opposite direction projects
the corresponding fields from an arbitrary `CorrectionAPI` at
`research/T17/probes/sobolev_closes.lean:86-118`.

The proof is mathematically substantive.  It recentres the Euclidean force and
proves support in the origin-centred cube
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:183-239`), obtains the
component `L¹_tH^s_x` rate from Paper1's endpoint interpolation
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:319-392`), constructs an
honest real-order datum path
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:127-181`), and transfers
the result back to the concrete periodized force
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:444-544`).

The extra assumptions are load-bearing rather than vacuity devices.  `ε₀ ≤ 1`
places every admitted scale in Paper1's `Ioc 0 1`
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:464-468`); `hv` supplies
the endpoint rates and smooth periodization
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:342-369`,
`formalization/NSFormalization/Section3/T17/Sobolev.lean:489-503`).  The other
cutoff and geometry assumptions are used to build `MemForceT` and the cube
support (`formalization/NSFormalization/Section3/T17/Sobolev.lean:467-495`).
Although `sobolevConst_pos` does not need its two range proofs because the
constant is positive for every real `s`, that strengthens rather than vacates
the requested statement (`formalization/NSFormalization/Section3/T17/Sobolev.lean:293-304`).

The report's non-vacuity theorem supplies a nonzero smooth periodic reference,
proves `0 < ε₀`, and instantiates both quantitative fields at `x₀=0`, `T=1`,
`r=1/4` (`research/T17/probes/sobolev_closes.lean:155-205`).  Thus the scale
interval is demonstrably nonempty.

### Hygiene

`git diff --name-only origin/erenup/integration-section3...HEAD` reports one new
formalization module and only research/log records otherwise; no pre-existing
Lean module was modified.  The formalization path is solely
`formalization/NSFormalization/Section3/T17/Sobolev.lean`.

The lane module, its positive probe, and its axiom file contain no
`sorry`, `admit`, declaration-level `axiom`, `native_decide`, or
`set_option maxHeartbeats` occurrence.  The module contains 25 declarations:
21 theorems and four definitions
(`formalization/NSFormalization/Section3/T17/Sobolev.lean:47-590`).  The supplied
axiom audit covers all 21 theorems
(`research/T17/axioms_u11.lean:3-23`), and every print has exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and review findings

1. **Medium, report/records only — the declared Fourier-convention gap is false as
   written.**  The report says that the angular/Mathlib dilation bridge is absent
   and that only two integer endpoint facts exist
   (`research/T17/REPORT_438.md:53`, `research/T17/REPORT_438.md:75`).  The same
   claim was copied to `research/T17/ATTEMPTS_U11.md:55-73`,
   `research/T17/T17_SPLIT.md:244-260`, and `logs/LESSONS.md:1`.

   The required whole-tree grep instead finds the pointwise convention identity
   `angularFourier f ξ = (2π)^(-3/2) • (Mathlib Fourier f) ((2π)⁻¹•ξ)` at
   `formalization/NSFormalization/Source/FourierConvention.lean:23-42`, the
   arbitrary-real-order weighted energy and norm equivalences at
   `formalization/NSFormalization/Source/FourierConvention.lean:49-143`, and their
   vector/time forms at
   `formalization/NSFormalization/Source/AngularForceNorms.lean:16-50`.  Section 4
   itself also cites the pointwise bridge at
   `formalization/NSFormalization/Section4/A01/CarrierBridge.lean:31-35`.

   What the searches did *not* find is a ready-made theorem stated directly as
   an `ENNReal` inequality from D01's homogeneous datum norm
   (`formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean:21-40`, whose
   compact value is identified in
   `formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean:40-58`)
   to Paper1's cycles-frequency inhomogeneous norm.  That narrower adapter may
   still be missing, but it is not a missing Fourier-convention/dilation theorem
   and the evidence does not justify calling it a separate analytic lane.
   This documentation defect does not affect the delivered alternate proof.

   **Exact fix:** replace every “no angularFourier/Mathlib-Fourier bridge; only endpoints”
   sentence with: “The arbitrary-real Fourier-convention equivalence exists in
   `Source/FourierConvention.lean:23-143` and `Source/AngularForceNorms.lean:19-50`;
   the tree search found no direct `ENNReal` adapter from
   `dotHomogeneousENorm`/`homogeneousFourierENorm` to the Paper1 norm required by
   the T13-localization route.”

2. **Low, report citations/count.**  The report points `sobolevConst` to line 283,
   `sobolevConst_pos` to 299, and `forceSobolev_memLp` to 547
   (`research/T17/REPORT_438.md:24-37`); their declaration lines are 275, 293,
   and 548 respectively.  It also calls the module's 21 theorems “21
   declarations” (`research/T17/REPORT_438.md:57`), whereas the module has 25
   declarations including four definitions.

   **Exact fix:** change those citations to `:275`, `:293`, `:548`, and change
   “21 declarations” to “25 declarations (21 theorems and four definitions; all
   21 theorems are axiom-audited).”

No mathematical or Lean-code gap remains in U11 itself.

## 4. Commands and results

All Lake commands were run from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

### Module build

Command:

```
lake build NSFormalization.Section3.T17.Sobolev
```

Exit 0.  Exact final line:

```
Build completed successfully (10014 jobs).
```

Lake also replayed warnings from pre-existing upstream modules; none points to
`Section3/T17/Sobolev.lean`.  The direct elaboration gate below is silent.

### Direct module elaboration

Command:

```
lake env lean ../formalization/NSFormalization/Section3/T17/Sobolev.lean
```

Exact output: empty.  Exit 0.

### Positive/conformance/non-vacuity probe

Command:

```
lake env lean ../research/T17/probes/sobolev_closes.lean
```

Exact output (exit 0):

```
'NSFormalization.Section3.T17.SobolevProbe.field_sobolevConst_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.SobolevProbe.field_forceSobolev_memLp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.SobolevProbe.field_force_sobolev_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.SobolevProbe.fields_at_placement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.SobolevProbe.nonvacuous_sobolev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Axiom audit

Command:

```
lake env lean ../research/T17/axioms_u11.lean
```

Exact output (exit 0):

```
'NSFormalization.Section3.T17.norm_scalar_datum_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.periodicSobolevSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.norm_datum_eq_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.norm_datum_eq_vector' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.periodicSobolevENorm_slice_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.periodicSobolevENorm_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.norm_datum_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_coefficient_path_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.shiftedForce_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.shiftedForce_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.shiftedForce_supportedInCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.periodize_shiftedForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.sobolev_endpoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.sobolevConst_summand_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.sobolevConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.fourierSobolevNorm_shifted' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.component_L1Hs_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.forceSobolevENormT_le_of_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.forceSobolev_memLp_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.forceSobolev_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_sobolev_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Negative mutation

The reviewer probe at `research/T17/probes/rev438_mutation.lean:22-43`
widens the main theorem from `s ≤ 1` to `s ≤ 2`; it does not remove an
argument.  Command:

```
lake env lean ../research/T17/probes/rev438_mutation.lean
```

It fails as required.  Exact error:

```
../research/T17/probes/rev438_mutation.lean:42:2: error: Type mismatch
  force_sobolev_bound nu hv x0 T delta r hvper O thetaR eps0 htheta heta hthetac hetac hthetasupp hetasupp hr2 heps0
    hepstime hepsspace
has type
  ∀ (s : ℝ),
    0 ≤ s →
      s ≤ 1 →
        ∀ ε ∈ Ioc 0 (correctionData v x0 T theta eta O thetaR eps0).ε₀,
          forceSobolevENormT 1 s (correctionForce nu v (correctionData v x0 T theta eta O thetaR eps0) ε) ≤
            ENNReal.ofReal (sobolevConst nu hv x0 T htheta heta hthetac hetac s * (ε ^ (3 / 2) + ε ^ (3 / 2 - s)))
but is expected to have type
  ∀ (s : ℝ),
    0 ≤ s →
      s ≤ 2 →
        ∀ eps ∈ Ioc 0 (correctionData v x0 T theta eta O thetaR eps0).ε₀,
          forceSobolevENormT 1 s (correctionForce nu v (correctionData v x0 T theta eta O thetaR eps0) eps) ≤
            ENNReal.ofReal (sobolevConst nu hv x0 T htheta heta hthetac hetac s * (eps ^ (3 / 2) + eps ^ (3 / 2 - s)))
```

### Repository gate

Command from the repository root:

```
LEAN_NUM_THREADS=6 make check
```

Exit 0.  The command's JSON closure dump exceeds the review harness's output
limit (the harness reported `original token count: 523222`); the exact retained
terminal result was:

```
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.055s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The preceding retained JSON showed `task_count: 45`, no
`missing_copied_imports`, `tracked_cache_free: true`, and
`base_compatibility_checked: false`; the latter is expected because plain
`make check` does not pass a base ref.

### Diff and conditional gates

Exact committed diff-name output against the requested base:

```
formalization/NSFormalization/Section3/T17/Sobolev.lean
logs/LESSONS.md
research/T17/ATTEMPTS_U11.md
research/T17/REPORT_438.md
research/T17/T17_SPLIT.md
research/T17/axioms_u11.lean
research/T17/probes/sobolev_closes.lean
```

`git diff --name-only origin/erenup/integration-section3...HEAD -- verification`
has exact empty output.  Therefore neither `verification/` nor its contracts
were touched, and the brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates are not
applicable.

Fixes required for the notes verdict:

1. Narrow the four “not in the tree” records to the missing direct homogeneous
   `ENNReal` adapter, and cite the existing arbitrary-real convention bridges.
2. Correct the three stale `Sobolev.lean` line citations and the declaration
   count in `REPORT_438.md`.
