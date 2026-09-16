ACCEPT

## 1. What the lane claims

The worker claims exactly the combined non-density part of Theorem 4.1(ii): for
real `q = 1` or `q = 2`, positive `nu,T`, and
`thresholds.exponent q 0 <= s`, every force in the zero-datum breakdown set has
norm bounded below by a positive radius; the radii are
`R43.criticalConst * nu` and `R44.radius nu T`, respectively
(`research/R41D/REPORT_232.md:5-11`).  It separately claims the corresponding
negation of `BreakdownDenseR`, a threshold-shaped bundle, and concrete instances
for both exponents (`research/R41D/REPORT_232.md:20-26`).  It expressly does not
claim the subcritical density or regular-reference rider fields
(`research/R41D/REPORT_232.md:37-42`).

These are faithful to the cited mathematics.  The paper fixes positive `nu,T`,
restricts `q` to `{1,2}`, and defines the threshold `2/q - 3/2`
(`paper/sections/04-whole-space.tex:8`); its zero-data clause is the iff
classification (`paper/sections/04-whole-space.tex:11`), and the proof obtains
the two closed endpoint obstructions from Propositions 4.3 and 4.4 followed by
Sobolev-order monotonicity (`paper/sections/04-whole-space.tex:179`).  The
proposed skeleton's field has precisely a threshold lower-bound premise, a
positive real radius, zero-datum breakdown membership, and a lower norm bound
(`research/section4/STATEMENTS.md:143-164`).

The cast choice is sound.  `ThresholdAPI.exponent` has a real `q`
(`verification/Contracts/V1/Thresholds.lean:10-18`), while the physical force
norm takes `q : ENNReal` (`verification/Contracts/V1/Data.lean:225-228`).  The
implementation retains the skeleton's real binder and uses `ENNReal.ofReal q`
(`formalization/NSFormalization/Section4/R41/NonDensity.lean:49-54`); the
mandatory case split at line 55 reduces this to the literal exponents consumed
by the q=1 and q=2 endpoint lemmas.  Changing the public binder to `ENNReal`
would cease to mirror the skeleton and its threshold record.

There is no hidden vacuity.  The statement uses neither `ENNReal.toReal` nor an
interval, and breakdown membership includes the actual smooth force class and
lifespan condition (`formalization/NSFormalization/Section4/R41/NonDensityL1.lean:57-79`).
The positivity assumptions are those of the paper; `hnu` makes the q=1 radius
positive and `hnu,hT` feed the q=2 endpoint proof
(`formalization/NSFormalization/Section4/R41/NonDensity.lean:60-69`).  Concrete
`nu=T=1` bundle instances exist for both q values, and concrete non-density
instances exist at both sharp endpoints
(`formalization/NSFormalization/Section4/R41/NonDensity.lean:106-124`).

## 2. What is in Lean

The report's declarations exist with the claimed statements:

- `RMainThresholds` copies all seven fields of `ThresholdAPI`, including the
  formula `exponent q s = 2/q - 3/2 - s`, token for token
  (`formalization/NSFormalization/Section4/R41/NonDensity.lean:23-33` versus
  `verification/Contracts/V1/Thresholds.lean:9-18`).  Its canonical value uses
  `Paper3.forceExponent` and the same witnesses as the registered binding
  (`formalization/NSFormalization/Section4/R41/NonDensity.lean:35-44` versus
  `verification/Bindings/Thresholds.lean:9-17`).
- `nonDensityZero_of_q` has the requested real-q quantifiers, positivity guards,
  threshold premise, positive radius, exact zero-datum breakdown set, and
  `ENNReal.ofReal q` norm (`formalization/NSFormalization/Section4/R41/NonDensity.lean:46-69`).
  Its two proof branches consume the exact endpoint results
  `criticalRadius_le_forceSobolevENorm`
  (`formalization/NSFormalization/Section4/R41/NonDensityL1.lean:81-98`) and
  `radius_le_forceSobolevENorm_L2`
  (`formalization/NSFormalization/Section4/R41/NonDensityL2.lean:13-29`).
- `not_breakdownDenseR_zero_of_q` has the same guards and proves the exact
  negation of the imported relative-density predicate
  (`formalization/NSFormalization/Section4/R41/NonDensity.lean:71-88`).  That
  predicate is the local verbatim form of `Data.BreakdownDenseR`
  (`formalization/NSFormalization/Section4/R41/NonDensityL1.lean:73-79` and
  `verification/Contracts/V1/Data.lean:702-708`).
- `RMainNonDensity` preserves the skeleton's binder order
  `nu,T,hnu,hT,q,hq,thresholds` and includes only the requested theorem field
  (`formalization/NSFormalization/Section4/R41/NonDensity.lean:90-104`).
- The verification-side conversion and bridges are explicit
  (`research/R41D/axioms_nondensity.lean:20-56`), and the contract-vocabulary
  lower-bound, non-density, and registered-witness theorems have the reported
  statements (`research/R41D/axioms_nondensity.lean:65-105`).

The substantive mutation is in
`research/R41/probes/rev232_widen_threshold.lean:11-32`.  It changes the main
premise from `exponent q 0 <= s` to `exponent q 0 - 1 <= s`, widening both
claimed ranges while copying the production proof unchanged.  Lean rejects
both branches at exactly the true endpoint recovery (`:22` and `:29`), so the
threshold constants are load-bearing.  This is not an argument-deletion test.

Hygiene passes.  No delivered declaration uses `sorry`, `admit`, `axiom`, or
`native_decide`; there is no `maxHeartbeats` setting.  Commit `5f1afda` adds the
implementation module rather than modifying an existing module.  Against the
requested current base, every implementation/record artifact in the diff is a
new file; no `verification/` path was touched, so the conditional
`scripts/gates.sh` and base-compatibility gate do not apply.

## 3. Gaps

There is no gap in the requested non-density clause.  The lane does not assemble
the full `RMainAPI`: `densityFixedInitial`, `densityZero`, and
`regularReferenceRider` remain outside its scope, exactly as reported.  Before
accepting that scope statement I searched the entire
`formalization/NSFormalization/Section4` tree.  The exact-name search returned
no match, the insertion-to-density shape search returned no match, and the
general density search found only the q=1/q=2 endpoint declarations and this
combined module under `Section4/R41`; the other hits concern unrelated analytic
density results.  Thus no existing R41 subcritical assembly lemma was overlooked.

The build command is not globally silent because Lake replays warnings from
pre-existing dependency modules.  It emits no diagnostic from
`NonDensity.lean`, and the direct module check has exactly zero output.  This is
already stated honestly in the worker report
(`research/R41D/REPORT_232.md:49-53`) and is not a lane defect.

## 4. Commands and results

All Lean/Lake commands were run after sourcing `scripts/lean-env.sh`; Lake ran
only from `verification/` with `LEAN_NUM_THREADS=6` and one command at a time.
Large replay output is represented by exact head/tail excerpts, following the
repository's review-log size rule.

### Build

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R41.NonDensity
exit 0; 17066 output bytes
⚠ [8781/9512] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
...
Build completed successfully (10554 jobs).
```

There was no line naming or diagnosing
`NSFormalization.Section4.R41.NonDensity`; all intervening lines were replayed
dependency warnings.

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R41/NonDensity.lean
exit 0; output bytes = 0
```

### Axiom/conformance audit

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41D/axioms_nondensity.lean
exit 0
'NSFormalization.Section4.R41.RMainThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.rMainThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.nonDensityZero_of_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.not_breakdownDenseR_zero_of_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.RMainNonDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.toRMainThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.rMainThresholds_exponent_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.breakdownSetIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.breakdownSetR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.breakdownSetRZero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.BreakdownDenseR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.nonDensityZero_of_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.not_breakdownDenseR_zero_of_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.registered_nonDensityZero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 14 reports are exactly `[propext, Classical.choice, Quot.sound]`.

### Repository checks

```text
$ LEAN_NUM_THREADS=6 make check
exit 0
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.CriticalRegularity"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/R41/NonDensity.lean
research/R41D/ATTEMPTS_NONDENSITY.md
research/R41D/REPORT_232.md
research/R41D/axioms_nondensity.lean

$ git diff --check origin/erenup/integration...HEAD
<no output; exit 0>

$ grep -nE '^[[:space:]]*(sorry|admit|axiom|native_decide)\b|:=[[:space:]]*(by[[:space:]]+)?(sorry|admit|native_decide)\b' formalization/NSFormalization/Section4/R41/NonDensity.lean research/R41D/axioms_nondensity.lean
<no output; exit 1 (no matches)>

$ grep -nE 'maxHeartbeats|set_option' formalization/NSFormalization/Section4/R41/NonDensity.lean research/R41D/axioms_nondensity.lean
<no output; exit 1 (no matches)>
```

No `verification/` path appears in the integration-range diff.  Therefore, per
the brief, `scripts/gates.sh` and
`experiments/check_contracts.py --base-ref origin/erenup/integration` were not
required.  `make check` did run the architecture-only `check_contracts.py`, as
shown above.

### Negative check

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41/probes/rev232_widen_threshold.lean
exit 1
../research/R41/probes/rev232_widen_threshold.lean:22:6: error: Type mismatch
  hs
has type
  -(1 / 2) <= s
but is expected to have type
  1 / 2 <= s
../research/R41/probes/rev232_widen_threshold.lean:29:6: error: Type mismatch
  hs
has type
  -(3 / 2) <= s
but is expected to have type
  -(1 / 2) <= s
```

Fixes: none.
