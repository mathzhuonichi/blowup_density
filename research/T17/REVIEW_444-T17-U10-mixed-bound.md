ACCEPT

## 1. What the lane claims

The worker claims a concrete-data implementation of the four U10 exports:
`mixedConst`, `mixedConst_nonneg`, `force_spatial_memLp`, and
`force_mixed_bound` (`research/T17/REPORT_444.md:3-55`).  Those declarations
exist with the reported statements at
`formalization/NSFormalization/Section3/T17/Mixed.lean:20-31` and
`:47-63`.

Statement fidelity checks:

- The canonical T17 fields require Haar `MemLp` slices for every
  `[Fact (1 <= p)]`, a real `mixedConst p q`, nonnegativity on `1 <= p,q`, and
  the bound with exponent `alphaT p q + 1`
  (`formalization/NSFormalization/Section3/T17/Correction.lean:242-261`).  The
  Spec has the same fields with contract `alpha`
  (`research/T17/Spec.lean:921-940`).  The lane's exact-field probe closes the
  copied result types by bare `exact` (`research/T17/probes/mixed_closes.lean:15-51`),
  and checks `alphaT p q = Contracts.V1.alpha p q` by `rfl` (`:53`).
- The manuscript states
  `||H_eps||_(L^q_t L^p_x) <= C_(p,q) eps^(-2+3/p+2/q)
   = C_(p,q) eps^(alpha(p,q)+1)` and says the constants are independent of
  sufficiently small `eps` (`paper/sections/03-torus.tex:232-242`); its proof
  explicitly includes the essential-supremum endpoints
  (`paper/sections/03-torus.tex:275-282`).  The lane has precisely that
  exponent (`formalization/NSFormalization/Section3/T17/Mixed.lean:87-94`).
- The constant is genuinely chosen before `eps`: it is the real value of the
  witness supplied by `physical_force_mixed_bound`
  (`formalization/NSFormalization/Paper1/CorrectionMixedNorms.lean:121-129`,
  `formalization/NSFormalization/Section3/T17/Mixed.lean:20-24`).  It does not
  exploit `top.toReal = 0`: the witness satisfies `C < top`, and the proof uses
  that fact in `ENNReal.ofReal_toReal hb.1.ne`
  (`formalization/NSFormalization/Section3/T17/Mixed.lean:83-86`).  At endpoint
  exponents, `p.toReal` or `q.toReal` being zero is the intended reciprocal
  exponent convention, not collapse of the coefficient
  (`formalization/NSFormalization/Paper1/CorrectionMixedNorms.lean:123-129`).
- The torus-to-Euclidean route is sound.  `force_eq` identifies the concrete
  force with the lattice lift of the one-copy force
  (`formalization/NSFormalization/Section3/T17/Transport.lean:278-291`);
  `source_force_tsupport` supplies its open-ball support
  (`formalization/NSFormalization/Section3/T17/ForceSupport.lean:114-127`);
  the exponent-generic Haar/Lebesgue equality is
  `eLpNorm_torusLift_eq_volume`
  (`formalization/NSFormalization/Section3/T15/Mixed.lean:126-136`); and
  `mixedLebesgueENormT_eq` attains the torus mixed-norm infimum on positive
  time (`formalization/NSFormalization/Section3/T15/Mixed.lean:232-262`).
  Finally, `Measure.restrict_le_self` is applied in the correct direction at
  `formalization/NSFormalization/Section3/T17/Mixed.lean:81-85`.
- The explicit hypotheses are honest.  Global `hv` is consumed by
  `physicalForce_smooth` and by the Paper1 mixed bound
  (`formalization/NSFormalization/Section3/T17/Mixed.lean:66-67,83`);
  `hcube` is consumed in the slice-support argument (`:68-80`); and `hε₀` is
  consumed when placing `eps` in `Ioc 0 1` (`:84-85`).  The unnamed `1 <= q`
  proof is not analytically needed by the stronger Paper1 theorem, but is the
  exact canonical T17 range (`Correction.lean:257`), so it is not a hidden or
  vacuity-producing input.

The admissible interval is not only conditionally quantified.  The existing
probe constructs a nonzero constant reference and proves a positive threshold
(`research/T17/probes/mixed_closes.lean:72-111`), then instantiates all three
exports, including the cube condition and `eps0 <= 1` (`:112-117`).  The probe
compiled during this review.

## 2. What is in Lean

The lane commit adds the single implementation module
`formalization/NSFormalization/Section3/T17/Mixed.lean` plus its requested
research records.  `git diff --name-status HEAD^ HEAD` shows the Lean module as
`A`, not a modification.  The required triple-dot comparison emits a
multiple-merge-base warning and also lists the inherited lane-439 T15 files,
but every changed Lean path is `A`; no existing Lean module is `M`.

The module contains no `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats` occurrence.  The direct module typecheck produces zero output.
All four module declarations print exactly
`[propext, Classical.choice, Quot.sound]`; the six printed probe declarations
do too (`research/T17/axioms_u10.lean:1-5`,
`research/T17/probes/mixed_closes.lean:120-126`).

The negative reviewer probe is
`research/T17/probes/rev444_mutated_exponent.lean`.  It changes the main
exponent from `alphaT p q + 1` to `alphaT p q + 2`; it does not remove an
argument.  Lean rejects it with the expected statement mismatch, reproducing
both exponents in the diagnostic.

## 3. Gaps

There is no residual U10 proof gap.

The worker correctly retains G1 as an assembly/spec issue: the canonical record
has `reference_periodic` but no global-smoothness field
(`formalization/NSFormalization/Section3/T17/Correction.lean:97-100`), while
this concrete theorem explicitly takes `hv : ContDiff ℝ ∞ v`
(`formalization/NSFormalization/Section3/T17/Mixed.lean:34-44`).  The requested
whole-tree checks were run before accepting that description:

```text
$ grep -rn 'reference_smooth' formalization/NSFormalization/Section4
[no output]

$ grep -rnE 'ContDiff ℝ ∞ v|physicalForce_smooth|physical_force_mixed_bound' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/R42/Assembly.lean:12:spacetime (`hv : ContDiff ℝ ∞ v`).
formalization/NSFormalization/Section4/I02/Reference.lean:8:Every correction lemma in `Paper1`/`Source` assumes `ContDiff ℝ ∞ v` on all of
formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean:109:theorem correction_scalar_homogeneous (nu : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean:173:theorem correction_componentTimeNorm (nu : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
formalization/NSFormalization/Section4/C01/VelocityJets.lean:28:  `ContDiff ℝ ∞ v ∧ ∀ n, MemLp (iteratedFDeriv ℝ n v) 2 volume`).
formalization/NSFormalization/Section4/D01/DatumToJets.lean:119:  ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume
formalization/NSFormalization/Section4/D01/DatumToJets.lean:124:  ContDiff ℝ ∞ v ∧ ∀ j ≤ m, MemLp (iteratedFDeriv ℝ j v) 2 volume
```

In particular, G1 is not a claim that the analytic truncation lemma is absent:
Section4 already supplies `exists_local_truncation`
(`formalization/NSFormalization/Section4/I02/Reference.lean:65-81`).  What
remains is to use such a bridge or amend the record during assembly, exactly as
the worker report says (`research/T17/REPORT_444.md:70-74`).  The report makes
no other "not in the tree" claim.

## 4. Commands and results

All Lean commands were run after sourcing `scripts/lean-env.sh`, one Lake
process at a time from `verification/`, with `LEAN_NUM_THREADS=6`.

### Module build

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Mixed
[223 lines: replayed warnings only from pre-existing dependencies]
Build completed successfully (10020 jobs).
```

The exact captured stdout/stderr is 13,501 bytes with SHA-256
`dfbba3a385eb604b28a3b45a95487bd16a8a0bc08ae9780b2f0cbea3f53a9054`.
Its exact capture wrapper output was:

```text
exit=0
  223 13501 /tmp/rev444_lake_build.txt
dfbba3a385eb604b28a3b45a95487bd16a8a0bc08ae9780b2f0cbea3f53a9054  /tmp/rev444_lake_build.txt

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10020 jobs).
```

No warning points to the reviewed module.

### Direct typechecks and axioms

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T17/Mixed.lean
[no output]
exit 0
```

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/mixed_closes.lean
'NSFormalization.Section3.T17.MixedProbe.field_force_spatial_memLp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.MixedProbe.field_force_mixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.MixedProbe.cubeCentre' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.MixedProbe.closure_ball_cubeCentre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.MixedProbe.nonvacuous_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.MixedProbe.field_mixedConst_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit 0
```

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T17/axioms_u10.lean
'NSFormalization.Section3.T17.mixedConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.mixedConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_spatial_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_mixed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

### Negative mutation

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/rev444_mutated_exponent.lean
../research/T17/probes/rev444_mutated_exponent.lean:32:2: error: Type mismatch
  force_mixed_bound nu hv x0 T delta r hvper O thetaR eps0 htheta heta hthetac hetac hthetasupp hetasupp hr2 hepstime
    hepsspace hcube heps0
has type
  ∀ (p q : ℝ≥0∞) [inst : Fact (1 ≤ p)],
    1 ≤ q →
      ∀ ε ∈ Ioc 0 (correctionData v x0 T theta eta O thetaR eps0).ε₀,
        mixedLebesgueENormT q p (correctionForce nu v (correctionData v x0 T theta eta O thetaR eps0) ε) ≤
          ENNReal.ofReal (mixedConst nu hv x0 T htheta heta hthetac hetac p q * ε ^ (alphaT p q + 1))
but is expected to have type
  ∀ (p q : ℝ≥0∞) [inst : Fact (1 ≤ p)],
    1 ≤ q →
      ∀ eps ∈ Ioc 0 (correctionData v x0 T theta eta O thetaR eps0).ε₀,
        mixedLebesgueENormT q p (correctionForce nu v (correctionData v x0 T theta eta O thetaR eps0) eps) ≤
          ENNReal.ofReal (mixedConst nu hv x0 T htheta heta hthetac hetac p q * eps ^ (alphaT p q + 2))
exit 1 (expected)
```

### Repository checks

`make check` passed twice.  The checker's closure inventory is very large; the
complete exact second capture is 2,170,111 bytes / 52,503 lines with SHA-256
`c7046c9dd6c332cccc8dd98cef3896f7611002b373596ec2975b92df72b23544`.
The exact capture summary and final output are:

```text
exit=0
  52503 2170111 /tmp/rev444_make_check.txt
c7046c9dd6c332cccc8dd98cef3896f7611002b373596ec2975b92df72b23544  /tmp/rev444_make_check.txt
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
Ran 13 tests in 0.047s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The opening output was:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 671,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
```

The reported copied-source token is pre-existing and is not in this module's
import closure or diff.  The lane-local forbidden-token grep had no output.

### Diff/hygiene gate

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 1c965400e3308df1cd679dfe843b0d5c47e49b82
formalization/NSFormalization/Section3/T15/Energy.lean
formalization/NSFormalization/Section3/T15/Mixed.lean
formalization/NSFormalization/Section3/T17/Mixed.lean
research/T15/ATTEMPTS_U4_U5.md
research/T15/REPORT_439.md
research/T15/T15_SPLIT.md
research/T15/axioms_u4_u5.lean
research/T15/probes/energy_mixed_closes.lean
research/T17/ATTEMPTS_U10.md
research/T17/REPORT_444.md
research/T17/T17_SPLIT.md
research/T17/axioms_u10.lean
research/T17/probes/mixed_closes.lean
```

No path under `verification/` is present.  Therefore the conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates were
not applicable.  `make check` nevertheless ran the ordinary contract checker
successfully.

No fixes required.
