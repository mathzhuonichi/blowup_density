ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims all eight U6 components, plus the path bridge and supporting
monotonicity/triangle lemmas, with the parallel-lane inputs left as explicit
premises for U9 (`research/T23/REPORT_485.md:5-36`).  It also claims five
declarations in `NormBridge.lean`, thirteen in `Rates.lean`, and the standard
three axioms for all eighteen (`research/T23/REPORT_485.md:40-50`).

The mathematical target is correctly identified.  The paper states the energy
rate `(M+D) ε^(1/2) + C ε^(3/2)`, the force rate
`C_s (ε^(1/2-s) + ε^(3/2-s))`, and convergence for negative `s` at
`paper/sections/03-torus.tex:287-310`.  Its bounded-domain transfer uses the
restriction norm for `0 ≤ s < 1/2`, contracts negative orders against the
zero-extension `L²` norm, and keeps support in one fixed interior compact set at
`paper/sections/03-torus.tex:647-664`.  The correction and packet supplier
rates themselves are at `paper/sections/03-torus.tex:122-158,220-284`.

The corresponding canonical fields are exactly the energy constant/rate at
`formalization/NSFormalization/Section3/T23/Boundary.lean:379-395`, the positive
force constant and subcritical rate at `Boundary.lean:397-418`, and the two
limits at `Boundary.lean:435-450`.  These agree with the research specification
at `research/T23/Spec.lean:934-973,990-1005`.  The raw `M,E` spelling in
`Boundary.lean` and the `P.energyBound,P.dissipationBound` spelling in
`Spec.lean` are both exercised by the delivered probe
(`research/T23/probes/T23-U6-rates-convergence_closes.lean:71-116`).

## 2. What is in Lean

All claimed declarations exist with the advertised statements.  The five
bridge declarations occupy
`formalization/NSFormalization/Section3/T23/NormBridge.lean:15-98`; the thirteen
rate declarations occupy
`formalization/NSFormalization/Section3/T23/Rates.lean:14-237`.  In particular:

- `lintegral_sobolevENorm_le_forceSobolevENorm` bounds every measurable path
  and then takes its infimum, including the empty-path case
  (`NormBridge.lean:13-24`).  This respects the actual infimum definitions at
  `Section4/D01/SmoothDatum.lean:314-320`,
  `Section4/D01/ForceClass.lean:145-153`, and
  `Section4/D01/HalfOrder.lean:138-144`.
- Whole-space and domain order lowering use genuine lowering maps and preserve
  the realized distribution (`NormBridge.lean:26-64`), matching the analogous
  T18/T15 shapes at `Section3/T18/SobolevRate.lean:138-168` and
  `Section3/T15/Convergence.lean:42-59,96-122`.
- Energy restriction separately contracts the velocity and gradient terms
  (`Rates.lean:13-24`).  `energyRate` keeps both powers and only replaces a
  possibly negative supplier constant by `max C 0` (`Rates.lean:26-59`).  The
  concrete probe consumes the registered `perturbationEnergyBound`, whose exact
  upstream type is at `verification/Contracts/V1/Scaling.lean:268-289`, and
  retains the matching correction/center/time (`T23-U6-rates-convergence_closes.lean:80-116`).
- The common force constant is fixed before `ε` and is strictly positive
  (`Rates.lean:61-68`).  The packet and correction estimates remain separate
  until `force_sum_rate` (`Rates.lean:91-121`), and the actual-family theorem has
  the exact canonical conclusion (`Rates.lean:123-178`).  The upstream q=1
  clauses are the registered fields at
  `verification/Contracts/V1/Scaling.lean:306-340`, instantiated in the probe at
  `T23-U6-rates-convergence_closes.lean:118-147`.
- Both convergence conclusions are the canonical domain norm and the right-hand
  filter `𝓝[>] 0` (`Rates.lean:197-237`).  The scalar squeeze lemma has the same
  powers at `Paper1/ScalingLimits.lean:10-16`.

The lead's parallel-lane concern is satisfied.  The hypotheses at
`Rates.lean:38-44,130-149` are the upstream formula, support/regularity facts,
U2b's separate energy/packet/correction estimates, and U5's left comparison.
They do not assume the combined U6 force rate or either convergence conclusion.
The two convergence helpers consume the already proved U6 rate, and the probe
passes `forceDifference_sobolev_bound` itself rather than an unrelated named
input (`T23-U6-rates-convergence_closes.lean:47-68`).  These are the approved
threaded facts for U9, not gaps.  There is no conclusion-shaped cross-lane
hypothesis and no drift from `Boundary.lean`/`Spec.lean`.

No vacuity device appears in the production modules: there is no `⊤.toReal`,
the finite right sides force honest norm bounds, and the canonical record also
has `eps_pos : 0 < ε₀` (`Boundary.lean:169-176`).  The successful reviewer probe
exhibits `1/2 ∈ Ioc 0 1`, `forceDiffSobolevConst 0 0 0 = 1`, and
`energyConst 2 = 2` (`research/T23/probes/rev485_nonvacuity.lean:9-19`).

The substantive negative mutation flips the sign of the strictly positive main
force constant from `C_s` to `-C_s` without removing an argument
(`research/T23/probes/rev485_mutation.lean:37-44`).  Lean rejects the unchanged
proof with the expected type mismatch, quoted in part 4.

## 3. Gaps and review findings

There is no U6 mathematical, Lean, axiom, or citation gap.  G0/G1 are expressly
outside this conditional unit (`research/T23/REPORT_485.md:60-71`).  The former
canonical-location gap is recorded as resolved by `Boundary.lean` at
`research/T23/SPEC_ISSUES.md:154-163`.  For the latter, the required whole-tree
search for an unrestricted smooth-domain integration-by-parts/no-slip theorem
returned no match in `formalization/NSFormalization/Section4` (exact command in
part 4); hence the report does not conceal a U6 lemma already present there.

The one required note is hygiene/report accuracy.  The report says
`git diff --check` exited 0 (`research/T23/REPORT_485.md:103-105`), but the
command currently fails on five whitespace-only lines in
`research/T23/ATTEMPTS_T23-U6-rates-convergence.md:118,124,130,136,145` and one
at `research/T23/probes/T23-U6-rates-convergence_closes.lean:48`.  This is not a
Lean or mathematical defect, but the recorded gate result is false at HEAD.

No forbidden proof token or heartbeat override occurs in either production
module, the delivered probe/axiom file, or the reviewer probes.  The recursive
local import traversal visits 402 `NSFormalization` modules and does not reach
`NSFormalization.Paper1.BoundaryCorollary`.  Relative to the lane's own merge
checkpoint `d15ba4da`, both production modules are additions (100 and 239 lines)
and no existing Lean module is modified.  The requested comparison with
`origin/erenup/integration-section3...HEAD` has multiple merge bases because the
lane was based on lane 480; its only `M` entries are records (`NEXT_SESSION.md`,
`SPEC_ISSUES.md`, `T23_SPLIT.md`), while every listed `.lean` module is `A`.

Exact one-line fix: strip the trailing whitespace at the six locations above
and rerun `git diff --check`, making the report's line 105 true.

## 4. Commands and results

Every Lean command sourced `scripts/lean-env.sh`; every Lake command ran from
`verification/` with `LEAN_NUM_THREADS=6`.

### Module builds

`lake build NSFormalization.Section3.T23.NormBridge` — exit 0.  First and last
output lines (the omitted middle consists only of dependency diagnostics):

```text
⚠ [8778/8910] Replayed NSFormalization.Source.FiniteHilbertBochner
...
Build completed successfully (10675 jobs).
```

`lake build NSFormalization.Section3.T23.Rates` — exit 0.  First and last output
lines (again, only dependency diagnostics in the omitted middle):

```text
⚠ [8778/9104] Replayed NSFormalization.Source.FiniteHilbertBochner
...
Build completed successfully (10677 jobs).
```

The following each exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T23/NormBridge.lean
lake env lean ../formalization/NSFormalization/Section3/T23/Rates.lean
lake env lean ../research/T23/probes/T23-U6-rates-convergence_closes.lean
lake env lean ../research/T23/probes/rev485_nonvacuity.lean
```

### Axiom audit

`lake env lean ../research/T23/axioms_T23-U6-rates-convergence.lean` — exit 0,
exact output:

```text
'NSFormalization.Section3.T23.lintegral_sobolevENorm_le_forceSobolevENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.sobolevENorm_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainSobolevENorm_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.forceSobolevENorm_add_le_of_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.domainEnergyENorm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.energyConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.energyConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.energyRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.forceDiffSobolevConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.forceDiffSobolevConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.positive_rates_absorb' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.force_sum_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.forceDifference_sobolev_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainForceSobolevENorm_mono_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.zeroExtForceSobolevENorm_mono_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.forceDifference_convergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.forceDifference_negativeSobolev_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.sobolevENorm_zeroExtension_nonpos_le_L2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Thus every declaration has exactly `[propext, Classical.choice, Quot.sound]`.

### Repository gate

`. scripts/lean-env.sh && make check` — exit 0.  Exact first and last excerpts
(within the raw-output limit):

```text
[first 40 lines]
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 733,
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
...
[last 40 lines]
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MultipleRegions"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The umbrella `BoundaryCorollary` token and `source_hashes_match: false` are the
pre-existing successful-gate output described by the worker, not imports of this
lane's modules.

No file under `verification/` is changed, so the brief's conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` do not apply:

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using b9eab7ff49606d56f033a7e76c835bf2ecbcaa5c
verification touched: no
scripts/gates.sh and check_contracts.py --base-ref origin/erenup/integration-section3: not applicable
```

### Negative and hygiene checks

`lake env lean ../research/T23/probes/rev485_mutation.lean` — expected exit 1:

```text
../research/T23/probes/rev485_mutation.lean:43:2: error: Type mismatch
  forceDifference_sobolev_bound place D reference force ε₀ A B he1 hformula hsupport hleft hF hH hpacket hcorr
has type
  ∀ (s : ℝ),
    0 ≤ s →
      s < 1 / 2 →
        ∀ ε ∈ Ioc 0 ε₀,
          (domainForceSobolevENorm Ω s fun z => force ε z - g z) ≤
            ENNReal.ofReal (forceDiffSobolevConst A B s * (ε ^ (1 / 2 - s) + ε ^ (3 / 2 - s)))
but is expected to have type
  ∀ (s : ℝ),
    0 ≤ s →
      s < 1 / 2 →
        ∀ ε ∈ Ioc 0 ε₀,
          (domainForceSobolevENorm Ω s fun z => force ε z - g z) ≤
            ENNReal.ofReal (-forceDiffSobolevConst A B s * (ε ^ (1 / 2 - s) + ε ^ (3 / 2 - s)))
```

Forbidden-token/heartbeat scan — exit 0, zero output:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b|set_option maxHeartbeats" \
  formalization/NSFormalization/Section3/T23/{NormBridge,Rates}.lean \
  research/T23/probes/T23-U6-rates-convergence_closes.lean \
  research/T23/axioms_T23-U6-rates-convergence.lean \
  research/T23/probes/rev485_{nonvacuity,mutation}.lean
```

Whole-Section4 missing-lemma search — no matches:

```text
$ grep -rnE 'IsBoundedBoxOrSmoothDomain|noSlip_uniqueness|smooth[- ]domain|regular[- ]level.*(integration|divergence)|divergence theorem.*boundary' formalization/NSFormalization/Section4
grep exit 1
```

`git diff --check origin/erenup/integration-section3...HEAD` — exit 2, exact
diagnostic lines and the reason for `ACCEPT-WITH-NOTES` (the offending end-of-line
spaces are rendered as `␠` so this review does not introduce them itself):

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using b9eab7ff49606d56f033a7e76c835bf2ecbcaa5c
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:118: trailing whitespace.
+␠␠
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:124: trailing whitespace.
+␠␠
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:130: trailing whitespace.
+␠␠
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:136: trailing whitespace.
+␠␠
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:145: trailing whitespace.
+␠␠
research/T23/probes/T23-U6-rates-convergence_closes.lean:48: trailing whitespace.
+example :␠
```

Final verdict: **ACCEPT-WITH-NOTES**.  Fix only the six trailing-whitespace
occurrences and rerun `git diff --check`; no theorem or hypothesis change is
requested.
