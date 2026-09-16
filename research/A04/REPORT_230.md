# Lane 230 report — A04 continuation V2 registration

## 1. Theorem registered

Registered `A04.continuation_v2`, witnessed by
`BlowupDensity.Bindings.continuationV2`. The record's five proved fields are:

1. `restart`: the owner-approved fixed-force H⁷ statement. For `ν > 0`, one
   `f ∈ F_R`, one `S ≥ 0`, and a finite `K`, all fixed before the existential,
   there is a real `δ > 0` which works for every `t₀ ∈ [0,S]` and every
   admissible datum `a'` with `sobolevENorm 7 a' ≤ K`;
2. `higherOrderBound`: the unchanged statement from `research/A04/Spec.lean`;
3. `restartBeyond`, `extendsBeyond`, and
   `lifespanInfiniteOfLocallyFinite`: the unconditional `MemForceR` shapes
   proved by lane 217's primed theorems.

`ContinuationV2API` is intentionally independent rather than an extension of
the draft/V1 A04 API. Extending that structure would inherit its unproved
`Restart` field and falsely make the stronger statement part of the witness.

## 2. Lean contents and registration

`verification/Contracts/V2/Continuation.lean` imports only
`Contracts.V1.Data`. It restates the five small Spec-local definitions needed
by the field statements and defines `RestartFixedForce` with the approved
quantifier order. It also defines
`ManuscriptHorizonLowerBoundH1` for documentation and drift detection only;
that proposition is not a structure field and has no proof.

The contract is parameterized by
`horizon : ℝ → SpatialField → SpaceTimeField → ℝ`.
`NSFormalization.Section4.A01.LocalTheoryBundle`, which defines the actual
`localHorizon'`, is absent from `experiments/check_contracts.py`'s
`CONTRACT_CANONICAL_MODULES`, so importing it into a versioned contract would
violate the contract boundary. `verification/Bindings/ContinuationV2.lean`
instantiates the parameter with `A01.localHorizon'` and proves the
`RestartFixedForce` correspondence by `rfl`. The data classes and norms have
the requested `rfl` bridges. The distinct `ClassicalSolutionR` structures are
transported field by field with `uniqueness_toA02` and
`maximalPartial_ofA02`; lifespan statements use
`maximalPartial_maximalLifespanR_eq` and the existing maximal-solution bridge.

`verification/Tests/ContinuationV2.lean` exports
`checkedContinuationV2`, runs `TestSupport.checkAxioms`, and gives conformance
examples for every field and the approved restart wording.
`research/A04/axioms_v2_contract.lean` additionally constructs an explicit
nonzero compact-bump force and a nonzero compactly supported divergence-free
curl datum. Applying `restart` to both produces a real `δ` with `0 < δ` and a
concrete lower bound on `A01.localHorizon'`; the hypotheses and conclusion are
therefore non-vacuous.

The registry count moves from 32 to 33. `A04.continuation_v2` has version 2,
parent `A04`, and an honest fixed-force/H⁷ scope. The A04 work item and the two
generated task views were updated with `python3 experiments/tasks.py render`.
`research/A04/ATTEMPTS_V2_CONTRACT.md` records the design attempts and refused
strengthenings; `research/A04/COMPARISON.md` now contains the required
“Paper vs V2” table.

## 3. Gap stated plainly: the paper's H¹ sentence is not proved

The following manuscript sentence is **NOT proved**:

> “The H¹ local existence bounds of the cited Theorems 5.1(ii) and 5.4(ii)
> then give a common positive existence duration when restarting at
> `t₀ ↑ S`.”

More formally, the paper/V1 proposition chooses one duration from H¹ datum and
force bounds uniformly across forces as well as restart times. The registered
V2 theorem does not imply it:

- an H⁷-bounded ball is smaller than an H¹-bounded ball, so an H⁷ theorem
  cannot be weakened to cover all H¹-bounded data;
- compactness of the shifted path of one fixed force does not give a duration
  uniform over the entire force class.

This is the exact limitation identified by `research/A04/REPORT_215.md` §3.
The open proposition remains named by `ManuscriptHorizonLowerBoundH1`, outside
the V2 structure. Proving it would require a forced quantitative H¹ local
theory on the mild stack with uniform dependence on the displayed H¹ datum and
force bounds.

The narrowed theorem is nevertheless sufficient for the formalized consumers:
`restartBeyond`, `extendsBeyond`, `lifespanInfiniteOfLocallyFinite`, and A02's
`exists_maximal` construction restart the same force using data whose H⁷ norms
are bounded by the Grönwall theorem. None uses cross-force uniformity. There is
no remaining gap in the five V2 fields themselves.

## 4. Validation and gate outputs

All Lean commands sourced `scripts/lean-env.sh`; Lake was invoked only from
`verification/` with `LEAN_NUM_THREADS=6`.

`scripts/gates.sh` exited 0. Its relevant terminal output was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.047s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/ContinuationV2.lean:26:0: Contract BlowupDensity.Tests.checkedContinuationV2: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The separately requested command
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
exited 0. Its closure arrays are large; the requested boundary values were:

```text
{
  "registered_contracts": 33,
  ...
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The full conformance command
`LEAN_NUM_THREADS=6 lake env lean ../research/A04/axioms_v2_contract.lean`
exited 0. Output:

```text
'BlowupDensity.Contracts.V2.Continuation.timeShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.squaredHTwoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.SolvesBelow' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.MemL1Hm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.IsMaximalSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.RestartFixedForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.ManuscriptHorizonLowerBoundH1' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.ContinuationV2API' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2_restartFixedForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2_manuscriptHorizonLowerBoundH1_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2_solvesBelow_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2_isMaximalSolution_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedContinuationV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonzeroForce_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonzeroForce_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonzeroDatum_mem_initialClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonzeroDatum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonvacuous_restart_nonzero_force_datum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The requested registry diff stat was:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` also exited 0. A declaration-anchored scan found no
`sorry`, `admit`, `axiom`, or `native_decide` in the four new Lean files.

## Lead corrections (review 230, 2026-09-17)

1. "uninhabited" → "unproved" wherever the H¹ sentence is described (it is an open proposition, not a claim of falsity).
2. A02's `exists_maximal'` (lane 213) does **not** depend on lane 179's Grönwall bound; it uses lane 211's `localHorizon'`/`localCarrier` only. The Grönwall bound enters the A04 continuation consumers (215/217), not maximal existence.
3. The contract's restated `timeShift` is **definitionally equal** to lane 160's (bridged by `rfl`), not a token-for-token copy.
