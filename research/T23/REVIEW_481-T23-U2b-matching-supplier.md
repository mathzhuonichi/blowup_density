ACCEPT

## 1. What the lane claims

The worker claims a registered, same-correction I02/I03 supplier; transport of
the correction and force to the original locally defined reference; the
correction energy, mixed-Lebesgue, and Sobolev-force estimates; and the two U2
cross-transport fields. The report also explicitly limits the radius to the
constructed inner radius `r / 2` and leaves the full boundary assembly and U6
force-difference comparison/convergence outside this lane
(`research/T23/REPORT_481.md:8-52`, `:79-102`).

I accept those claims. In particular, I do **not** treat canonical upstream
field hypotheses as gaps: the lead-approved pattern is visible in the
production transport lemmas, while the contract-facing theorem actually
constructs the registered `C` and `A` rather than taking them as hypotheses
(`research/T23/probes/T23-U2b-matching-supplier_closes.lean:1260-1298`). There
is no conclusion-shaped named input.

Statement fidelity against the paper and canonical statements:

- The manuscript defines the local potential/correction and cancellation at
  `paper/sections/03-torus.tex:176-215`; the energy, mixed, and `q = 1`
  Sobolev rates are exactly `ε^(3/2)`, `ε^(alpha(p,q)+1)`, and
  `ε^(3/2)+ε^(3/2-s)` at `paper/sections/03-torus.tex:218-242`.
  The generalized registered Sobolev rate in the delivered theorem is
  `ε^(2/q.toReal-1/2)+ε^(2/q.toReal-1/2-s)`, which specializes at `q=1` to
  the paper's rate
  (`research/T23/probes/T23-U2b-matching-supplier_closes.lean:1281-1285`).
- The registered I02 fields have the exact energy and mixed statements at
  `verification/Contracts/V1/Correction.lean:474-510`; the I03 correction
  Sobolev statement is at `verification/Contracts/V1/Scaling.lean:327-340`,
  and its same-`C` contract is explicit at
  `verification/Contracts/V1/Scaling.lean:471-482`.
- The two U2 conclusions match `Spec.lean` exactly
  (`research/T23/Spec.lean:879-891`) and match the canonical interface
  (`formalization/NSFormalization/Section3/T23/Boundary.lean:318-336`). The
  four exact consumers check both spellings without extra hypotheses
  (`research/T23/probes/T23-U2b-matching-supplier_closes.lean:1445-1476`).
- The paper's boundary corollary and proof require localization to an interior
  ball and domain norms at `paper/sections/03-torus.tex:632-664`. The lane does
  not overclaim the final corollary or the U6 domain force-difference estimate;
  those are different canonical fields at
  `formalization/NSFormalization/Section3/T23/Boundary.lean:379-418`.

## 2. What is in Lean

Every theorem named in the worker report exists with the claimed statement:

- `correction_eq_physical`, `local_match`, and `local_crossTransport` are at
  `formalization/NSFormalization/Section3/T23/MatchingSupplier.lean:14-88`.
  `local_match` proves equality of the actual correction and force using local
  cylinder agreement; `local_crossTransport` concludes both actual
  directional-derivative equalities on `Ico 0 C.T`.
- The literal seven-field cutoff and its force transport are at
  `formalization/NSFormalization/Section3/T23/MatchingSupplier.lean:90-108`;
  the domain reference supplies the precise local smoothness/divergence fields
  at `:110-123`.
- Domain energy restriction, transported energy and mixed bounds, the angular
  path upper bound, and the independently proved uniform-threshold local
  Sobolev estimate are at
  `formalization/NSFormalization/Section3/T23/CorrectionEstimates.lean:15-133`.
- The registered bridge is not a placeholder. It calls
  `Bindings.correctionV2` and `Bindings.scaling` at
  `research/T23/probes/T23-U2b-matching-supplier_closes.lean:1291-1298`, proves
  the scaling threshold did not shrink for this witness at `:1299-1303`, and
  returns `A.correction = C`, the matching `D`, all three estimates, and both
  cross terms at `:1266-1338`. The seven-field variant is proved at
  `:1340-1410`, and the actual `ClassicalSolutionOmega` instance at
  `:1412-1427`.
- The inner-radius convention is honest. The spatial extension agrees only on
  `ball x₀ (r/2)`
  (`formalization/NSFormalization/Section3/T23/SpatialExtension.lean:13-43`),
  and both registered bridge statements explicitly return `C.r = r/2`
  (`research/T23/probes/T23-U2b-matching-supplier_closes.lean:1266-1271`,
  `:1348-1353`).

Non-vacuity and hypothesis audit:

- `hT`, `hδ`, and `hr` are strict positivity hypotheses and feed the actual
  extension/registered constructors
  (`research/T23/probes/T23-U2b-matching-supplier_closes.lean:1260-1295`).
  Local smoothness and divergence are used by
  `exists_spatial_solenoidal_extension`, whose construction is a curl of a
  cutoff potential
  (`formalization/NSFormalization/Section3/T23/SpatialExtension.lean:16-42`).
- The conclusion includes `0 < D.ε₀` and uses `Ioc 0 D.ε₀`
  (`research/T23/probes/T23-U2b-matching-supplier_closes.lean:1269-1286`), so
  neither an empty interval nor `⊤.toReal = 0` makes the theorem vacuous.
  The additional passing probe chooses the concrete scale `ε=e` and applies
  the actual energy bound
  (`research/T23/probes/rev481_nonvacuity.lean:10-21`).
- Energy constants are explicitly nonnegative and mixed/Sobolev constants are
  strictly positive (`CorrectionEstimates.lean:28-64` and
  `T23-U2b-matching-supplier_closes.lean:1275-1285`). The Sobolev theorem has
  `1 ≤ q` and `0 ≤ s ≤ 1`; allowing `q=⊤` is the registered strengthening, not
  a vacuity (`verification/Contracts/V1/Scaling.lean:310-340`).

The axiom audit is exact. The production audit contains 11 guarded
`#print axioms` commands
(`research/T23/axioms_T23-U2b-matching-supplier.lean:3-45`), and the probe has
eight more (`research/T23/probes/T23-U2b-matching-supplier_closes.lean:1479-1509`).
Every guard expects exactly `[propext, Classical.choice, Quot.sound]`; direct
elaboration is silent and successful, so all 19 expectations match.

## 3. Gaps and hygiene

There is no blocking gap in the lane's assigned result.

The worker's declared out-of-scope items were checked against the entire
`formalization/NSFormalization/Section4` tree as required:

```text
$ grep -rnE 'structure ScalingAPI|def scaling([^A-Za-z_]|$)|theorem scaling([^A-Za-z_]|$)|A\.correction = C|correctionPositiveScaling' formalization/NSFormalization/Section4 --include='*.lean'
(no output)
$ grep -rnE 'BoundaryInsertionAPI|boundaryInsertionStatement|IsMaximalDomainSolution|ClassicalSolutionOmega' formalization/NSFormalization/Section4 --include='*.lean'
(no output)
$ grep -rnE 'force.*(convergence|tendsto)|negativeSobolev|forceDifference.*bound|perturbationEnergyBound' formalization/NSFormalization/Section4 --include='*.lean'
(no output)
```

A broader path/slice grep found only unrelated Section4 path machinery (for
example `Section4/R42/CorrectionPath.lean:180` and
`Section4/I02/Mixed.lean:16,50`), not the T23 domain
`domainForceSobolevENorm`/`zeroExtForceSobolevENorm` comparison claimed as U6
work. Thus the report's gap boundaries are honest.

Hygiene passes:

- No delivered production or probe code contains `sorry`, `admit`, `axiom`,
  `native_decide`, or `set_option maxHeartbeats`. The only grep hits are prose
  in the copied Spec comments at
  `research/T23/probes/T23-U2b-matching-supplier_closes.lean:22,97,545`.
  The forbidden `Paper1/BoundaryCorollary` is cited in comments at `:95,544`
  and is not imported.
- The required
  `git diff --name-only origin/erenup/integration-section3...HEAD` reports a
  multiple-merge-base warning and lists the inherited lane-480 files plus this
  lane's files. `--name-status` marks every listed Lean module `A`, not `M`.
  Relative to this lane's actual briefed base `b5f0ab6c`, the only production
  Lean files are the two new modules
  `CorrectionEstimates.lean` and `MatchingSupplier.lean`; no existing Lean
  module was modified.
- No path under `verification/` appears in the required diff, so the
  conditional `scripts/gates.sh` and
  `check_contracts.py --base-ref origin/erenup/integration-section3` gates are
  not triggered.
- `git diff --check` exits 0. The pre-existing untracked collaboration brief
  remains untouched. This review adds only the two permitted `rev481_*.lean`
  probes and this required report.

The substantive negative mutation is
`research/T23/probes/rev481_mutation.lean:11-26`: it widens the scale interval
from `(0,e]` to `(-1,e]` without dropping an argument. The production proof
then fails for the intended reason:

```text
../research/T23/probes/rev481_mutation.lean:26:51: error: Application type mismatch: The argument
  hε
has type
  ε ∈ Ioc (-1) e
but is expected to have type
  ε ∈ Ioc 0 e
in the application
  WholeSpaceCorrectionAPI.local_crossTransport C hK hv hdiv hu he ε hε
```

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; every `lake` command ran from
`verification/` with `LEAN_NUM_THREADS=6`.

1. Module builds:

Exact first and last output lines:

```text
$ lake build NSFormalization.Section3.T23.MatchingSupplier
⚠ [8778/9027] Replayed NSFormalization.Source.FiniteHilbertBochner
Build completed successfully (10088 jobs).

$ lake build NSFormalization.Section3.T23.CorrectionEstimates
⚠ [8778/8908] Replayed NSFormalization.Source.FiniteHilbertBochner
Build completed successfully (10093 jobs).
```

Only upstream replayed diagnostics occur between the quoted exact first and
last lines; neither lane module emits a diagnostic. Both exits were 0.

2. Direct elaboration, probe, and axioms gates:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T23/MatchingSupplier.lean
(no output; exit 0)
$ lake env lean ../formalization/NSFormalization/Section3/T23/CorrectionEstimates.lean
(no output; exit 0)
$ lake env lean ../research/T23/probes/T23-U2b-matching-supplier_closes.lean
(no output; exit 0)
$ lake env lean ../research/T23/axioms_T23-U2b-matching-supplier.lean
(no output; exit 0)
$ lake env lean ../research/T23/probes/rev481_nonvacuity.lean
(no output; exit 0)
```

3. Required negative check:

```text
$ lake env lean ../research/T23/probes/rev481_mutation.lean
[the exact six-line error is quoted in part 3]
exit 1
```

4. Repository check:

Exact first output excerpt:

```text
$ make check
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
```

Exact last output excerpt:

```text
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Exact result: `exit=0`, `67332` output lines, `2795061` bytes. The displayed
first and last excerpts are within the 40-line-per-end limit. The copied
umbrella warning and `source_hashes_match: false` are pre-existing inventory
facts; the gate itself passed.

5. Diff/hygiene result:

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using b9eab7ff49606d56f033a7e76c835bf2ecbcaa5c
NEXT_SESSION.md
formalization/NSFormalization/Section3/T23/Boundary.lean
formalization/NSFormalization/Section3/T23/CorrectionEstimates.lean
formalization/NSFormalization/Section3/T23/Geometry.lean
formalization/NSFormalization/Section3/T23/MatchingSupplier.lean
formalization/NSFormalization/Section3/T23/WholeSpaceCorrection.lean
research/T23/ATTEMPTS_T23-U2b-matching-supplier.md
research/T23/ATTEMPTS_UCAN.md
research/T23/REPORT_480.md
research/T23/REPORT_481.md
research/T23/SPEC_ISSUES.md
research/T23/T23_SPLIT.md
research/T23/audit_481.log
research/T23/axioms_481.log
research/T23/axioms_T23-U2b-matching-supplier.lean
research/T23/axioms_ucan.lean
research/T23/build_481_final.log
research/T23/check_481.log
research/T23/mutations_481.log
research/T23/probes/T23-U2b-matching-supplier_closes.lean
research/T23/probes/boundary_api_on_canonical.lean

$ git diff --name-status b5f0ab6c..HEAD
A formalization/NSFormalization/Section3/T23/CorrectionEstimates.lean
A formalization/NSFormalization/Section3/T23/MatchingSupplier.lean
A research/T23/ATTEMPTS_T23-U2b-matching-supplier.md
A research/T23/REPORT_481.md
M research/T23/T23_SPLIT.md
A research/T23/audit_481.log
A research/T23/axioms_481.log
A research/T23/axioms_T23-U2b-matching-supplier.lean
A research/T23/build_481_final.log
A research/T23/check_481.log
A research/T23/mutations_481.log
A research/T23/probes/T23-U2b-matching-supplier_closes.lean
```

No fix is required.
