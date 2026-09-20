ACCEPT

## 1. What the lane claims

The worker accurately describes this lane as an honest partial, not as a proof
of the complete local `ScalingAPI.forceConvergence` field
(`research/T15/REPORT_458.md:5-7`).  Its principal claim is the literal `q = 1`
specialization

```lean
theorem forceConvergence_one
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < criticalOrder ((1 : ℝ≥0∞).toReal) →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (periodizedScaledForce f place.x₀ place.T ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0)
```

and the report reproduces it exactly (`research/T15/REPORT_458.md:9-20` versus
`formalization/NSFormalization/Section3/T15/Convergence.lean:101-110`).  The
other three claimed declarations also exist with the described statements:

- `persistenceDown_norm_le_one` is the genuine datum contraction
  (`formalization/NSFormalization/Section3/T15/Convergence.lean:32-36`), backed
  by the tree theorem at
  `formalization/NSFormalization/Section3/T11/HighOrder.lean:167-174`.
- `forceSobolevENormT_mono_order` quantifies every `q`, every ordered pair
  `s ≤ r`, and every physical force, with no added path premise
  (`formalization/NSFormalization/Section3/T15/Convergence.lean:44-59`).  It
  constructs the lower-order path rather than identifying the phantom-indexed
  datum types (`formalization/NSFormalization/Section3/T15/Convergence.lean:50-57`).
- `forceConvergence_one_nonnegative` has exactly the range `0 ≤ s < 1/2`
  and the same explicit force family and right-neighborhood filter
  (`formalization/NSFormalization/Section3/T15/Convergence.lean:66-75`).  Its
  use of the U13 bound and `Ioc_mem_nhdsGT place.eps_pos` is visible at
  `formalization/NSFormalization/Section3/T15/Convergence.lean:91-94`.

This is the mathematics actually stated by Proposition 3.3: the manuscript
gives the `L¹_t H^s_x` estimate and concludes convergence for every `s < 1/2`
(`paper/sections/03-torus.tex:133-138`), with the negative-order reduction to
order zero explained at `paper/sections/03-torus.tex:150-158`.  The local
canonical record deliberately promotes that conclusion to `q ∈ {1,2}`
(`formalization/NSFormalization/Section3/T15/Scaling.lean:439-452`); hence the
proved theorem is the full manuscript conclusion but only the `q = 1` branch
of the promoted lane field.

The hypotheses are honest.  `forceSobolevENormT` is an infimum over actual
measurable periodic datum paths, not a `toReal` encoding
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:218-230`).
`PlacementData` requires both `T > 0` and `ε₀ > 0`, so neither the time nor
scale interval is empty
(`formalization/NSFormalization/Section3/T15/Scaling.lean:106-115` and
`:165-190`).  The proof contains no `⊤.toReal = 0` step.  `hf`, `hc`, and
`place` are all consumed by `packetSobolevBound`
(`formalization/NSFormalization/Section3/T15/Convergence.lean:93-94`); there is
no named input or hidden bridge assumption.

Non-vacuity is already supplied by the worker: the probe defines a concrete
time/space bump force (`research/T15/probes/convergence_closes.lean:39-49`), a
placement with `T = 1` and `ε₀ = 1/2`
(`research/T15/probes/convergence_closes.lean:138-160`), and proves both that
the force is nonzero and that the theorem applies
(`research/T15/probes/convergence_closes.lean:162-177`).  The probe typechecks
with zero output, as recorded below.

## 2. What is in Lean

The new module contains exactly the four declarations claimed by the report:
`persistenceDown_norm_le_one`, `forceSobolevENormT_mono_order`,
`forceConvergence_one_nonnegative`, and `forceConvergence_one`
(`formalization/NSFormalization/Section3/T15/Convergence.lean:32-122`).  The
axiom audit lists those same four declarations and no others
(`research/T15/axioms_u14.lean:5-8`).

The proof is mathematically aligned with the cited sources:

- `criticalOrder q = 2/q - 3/2` is the registered definition
  (`verification/Contracts/V1/Data.lean:256-265`) and is copied literally into
  the local T15 specification
  (`formalization/NSFormalization/Section3/T15/Scaling.lean:52-53`).
- The packet exponent is literally
  `alphaT p q = -3 + 3/p.toReal + 2/q.toReal`
  (`formalization/NSFormalization/Section3/T15/Bridges.lean:74-79`), matching
  the paper (`paper/sections/03-torus.tex:129-131`).
- The upper bound used in the squeeze is the proved U13 theorem over every
  admissible scale (`formalization/NSFormalization/Section3/T15/SobolevBound.lean:197-206`).
- The Section 4 analogue really is a whole-space `q ∈ {1,2}` result
  (`verification/Contracts/V1/Scaling.lean:416-432`), and its binding splits
  into distinct whole-space `L¹` and `L²` limit theorems
  (`verification/Bindings/Scaling.lean:599-628`).  It does not itself furnish
  the missing torus periodization transfer.

The worker commit adds the Lean module rather than modifying an existing
formalization module.  Exact `git show --name-status HEAD` payload:

```text
A	formalization/NSFormalization/Section3/T15/Convergence.lean
A	research/T15/ATTEMPTS_U14.md
A	research/T15/REPORT_458.md
M	research/T15/T15_SPLIT.md
A	research/T15/axioms_u14.lean
A	research/T15/probes/convergence_closes.lean
```

The requested comparison against `origin/erenup/integration-section3` warned
that the history has multiple merge bases and selected
`6a07f394ae8ab57027968df7da87e0acf6e83995`.  Its exact name-status output was:

```text
M	PLAN.md
A	collaboration/briefs/455-T18-U12-assembly-registration.md
A	collaboration/briefs/456-T15-U12-U13-force-sobolev.md
A	collaboration/briefs/457-T19-UCAN-canonical-record.md
A	formalization/NSFormalization/Section3/T15/Convergence.lean
A	formalization/NSFormalization/Section3/T18/EnergyRate.lean
A	formalization/NSFormalization/Section3/T18/MixedRate.lean
M	logs/AGENT_RUNS.csv
A	research/T15/ATTEMPTS_U14.md
A	research/T15/REPORT_458.md
A	research/T15/REVIEW_450-T15-U9-sobolev-path.md
M	research/T15/T15_SPLIT.md
A	research/T15/axioms_u14.lean
A	research/T15/probes/convergence_closes.lean
A	research/T15/probes/rev450_nonvacuity.lean
A	research/T15/probes/rev450_widened_horizon.lean
A	research/T18/ATTEMPTS_U9_U10.md
A	research/T18/REPORT_443.md
A	research/T18/REVIEW_443-T18-U9-U10-energy-mixed-rates.md
M	research/T18/T18_SPLIT.md
A	research/T18/axioms_u9_u10.lean
A	research/T18/probes/rev443_mutation.lean
A	research/T18/probes/rev443_nonvacuity.lean
A	research/T18/probes/u9_u10_closes.lean
```

Thus no pre-existing `formalization/.../*.lean` module is marked modified;
the additional added modules are inherited branch history, while the HEAD
commit payload above isolates lane 458.

The forbidden-token scan

```text
rg -n "\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom\b" \
  formalization/NSFormalization/Section3/T15/Convergence.lean \
  research/T15/probes/convergence_closes.lean research/T15/axioms_u14.lean
```

had exactly no output.  The heartbeat scan had exactly:

```text
formalization/NSFormalization/Section3/T15/Convergence.lean:43:set_option maxHeartbeats 400000 in
```

This is declaration-local, at the permitted ceiling, and immediately preceded
by the explanatory comment at
`formalization/NSFormalization/Section3/T15/Convergence.lean:42`.  Direct
typechecking gives no warnings from the module.  `git diff --check
origin/erenup/integration-section3...HEAD` had no output apart from the same
multiple-merge-base warning.

## 3. Gaps

The full local field remains open at exactly

```lean
∀ s : ℝ, s < criticalOrder ((2 : ℝ≥0∞).toReal) →
  Tendsto
    (fun ε : ℝ ↦ forceSobolevENormT 2 s
      (periodizedScaledForce f place.x₀ place.T ε))
    (𝒩[>] 0) (𝒩 0)
```

as the report says (`research/T15/REPORT_458.md:48-80`).  The arithmetic
obstruction in the brief is real: substituting `p = q = 2` in the registered
formula gives `alphaT 2 2 = -1/2`, not `+1/2`
(`formalization/NSFormalization/Section3/T15/Bridges.lean:78-79`).  The review
probe independently checks this equality, together with the two critical
orders (`research/T15/probes/rev458_widened_critical_order.lean:12-21`).
Consequently the proposed comparison to order zero grows like
`ε^(-1/2)` and cannot prove the `q = 2` branch.

The reported whole-space replacement does exist:
`compact_scalar_force_L2_tendsto` and
`compact_vector_force_L2_tendsto` cover every `s < -1/2`
(`formalization/NSFormalization/Source/CompactForceConvergence.lean:96-131`).
The existing periodic adapter, however, is explicitly only an `L¹` theorem
and compares negative order to whole-space order zero
(`formalization/NSFormalization/Paper1/PeriodicNonpositiveForce.lean:65-100`).

I checked the worker's "not in the tree" claim with the required whole-Section
4 searches.  Exact results:

```text
$ grep -rnE "forceConvergence|periodic_nonpositive.*L2|periodi(ze|zed).*(L2|L²).*tendsto|L2.*periodi(ze|zed).*tendsto|negative.order.*periodi(ze|zed)" formalization/NSFormalization/Section4
# exit 1; no output

$ grep -rnE "compact_(scalar|vector)_force_L2_tendsto|force_negative_tendsto_zero|negative_intermediate_index|periodicVectorSobolevNorm" formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/R41/NonDensity.lean:43:  negativeIndex := fun _ hs => Paper3.negative_intermediate_index hs

$ grep -rnE "periodic_nonpositive.*L2|periodic.*L2.*tendsto|L2.*periodic.*tendsto|periodize.*L2.*tendsto|L2.*periodize.*tendsto" formalization/NSFormalization
# exit 1; no output
```

The only Section 4 hit is unrelated index selection, so the declared torus
`L²_t H^s_x` transfer gap is supported.  The lane brief explicitly permits
delivery of the other branches with the exact residual when such an in-tree
bridge is genuinely absent; therefore this residual does not invalidate the
honest partial.

For the required negative test I widened the main `q = 1` interval from
`s < criticalOrder 1 = 1/2` to
`s < criticalOrder 1 + 1 = 3/2`
(`research/T15/probes/rev458_widened_critical_order.lean:23-32`).  This changes
a substantive critical constant and does not drop an argument.  The proof
breaks exactly as expected:

```text
../research/T15/probes/rev458_widened_critical_order.lean:32:2: error: Type mismatch
  forceConvergence_one hf hc place
has type
  ∀ s < criticalOrder (ENNReal.toReal 1),
    Tendsto (fun ε => forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε)) (𝒩[>] 0) (𝒩 0)
but is expected to have type
  ∀ s < criticalOrder (ENNReal.toReal 1) + 1,
    Tendsto (fun ε => forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε)) (𝒩[>] 0) (𝒩 0)
```

## 4. Commands and results

Every Lean command below was run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

1. Module build:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Convergence
Build completed successfully (10024 jobs).
```

The raw build also replayed warnings from existing upstream modules
(`FiniteHilbertBochner`, `PeriodicSobolevHilbert`,
`EndpointSafeTwoSpacePicard`, and others); it emitted no warning or error from
`NSFormalization.Section3.T15.Convergence`.  Exit code was 0.

2. Direct module check:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/Convergence.lean
# exit 0; no output
```

3. Conformance/non-vacuity probe:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/convergence_closes.lean
# exit 0; no output
```

4. Axiom audit, exact output:

```text
'NSFormalization.Section3.T15.persistenceDown_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.forceSobolevENormT_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.forceConvergence_one_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.forceConvergence_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit code was 0, and every declaration has exactly the permitted set.

5. Repository check: `make check` exited 0.  It prints the full generated
architecture closure; its exact terminal tail was:

```text
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.ConservativeForcing"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

No path under `verification/` appears in either the HEAD commit payload or
`git diff --name-only origin/erenup/integration-section3...HEAD`; the latter
check for `^verification/` had no output.  Therefore the brief's conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates were not triggered.  (`make check`
did independently run the ordinary architecture contract check.)

Fixes: none.
