# T16 lane 371 report

## 1. What is registered

`T02.local_potential` V1 registers the reconciled T16 form of
`lem:potential`: the four periodic physical-layer helpers, seven-field
`CutoffData`, 26-field `LocalPotentialAPI`, and `localPotentialStatement`.
The contract is transported from `NSFormalization.Section3.T16.localPotential`
by `verification/Bindings/LocalPotential.lean`; the structure exception uses
fieldwise conversions and `rfl` round trips. No correction norm bound is
asserted; that remains T17.

## 2. Lean and test deliverables

The contract, binding, and test files are
`verification/Contracts/V1/LocalPotential.lean`,
`verification/Bindings/LocalPotential.lean`, and
`verification/Tests/LocalPotential.lean`. The test now includes:

* an independent, token-for-token restatement of the Spec's
  `localPotentialStatement` quantifiers;
* an independent equivalence spelling out all 26 `LocalPotentialAPI` fields;
* the nonzero constant-field instance `v = coordinateVector 0`, `U = 0`,
  `K = {0}`, `r = 1/4`, `T = δ = 1`, discharged through
  `Bindings.localPotential`; and
* the witness `(coordinateVector 0 : Space) ≠ 0`.

The axiom audit is in `research/T16/axioms_contract.lean`. The reviewer
probes `research/T16/probes/rev371_mutation.lean` and
`research/T16/probes/rev371_nonvacuity.lean` are retained and included with
this fix. `research/T16/ATTEMPTS_CONTRACT.md` now calls the helper bridges
“whole-function `rfl` bridges”.

## 3. Scope and remaining gap

The registered theorem supplies the Urysohn cutoffs, positive common
threshold, local radial potential/curl statement, and the unit-periodic
lattice-lift correction with all seven `correction_*` clauses, including
`eq:bgzero`. The correction norm estimate is intentionally not part of this
contract and remains assigned to T17.

## 4. Commands and results

Lean environment: `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`; Lean commands
run from `verification/`.

```text
$ BASE_REF=origin/erenup/integration-section3 scripts/gates.sh
== make check
45 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/LocalPotential.lean:13:0: Contract BlowupDensity.Tests.checkedLocalPotential: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
[exit 0]
```

The explicit base-aware registry check also exited 0:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
{
  "registered_contracts": 41,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The local test and axiom file both elaborate successfully. The axiom file
prints exactly:

```text
'BlowupDensity.Tests.checkedLocalPotential' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The registry diff relative to the integration base is append-only:

```text
$ git diff --stat origin/erenup/integration-section3...HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```
