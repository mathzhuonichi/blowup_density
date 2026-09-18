# T13 lane 379 contract-registration report

## 1. What theorem is registered

`T02.localization` V1 registers the reconciled T13
`LocalizationAPI : Prop` for `paper/sections/03-torus.tex:22-98`.  Its six
fields state:

- strict positivity and finiteness of the explicit Gagliardo constant
  `cFrac s` for `0 < s < 1`;
- the whole-space Gagliardo identity using the registered
  `dotHomogeneousENorm` and the torus identity using T10's homogeneous norm of
  `meanZeroPartT f`, both with the same explicit `cFrac`;
- the uniform localization estimate, with one positive real constant selected
  before every smooth field supported in the fixed admissible ball; and
- the `s=0` physical `L²` and `s=1` Hilbert--Schmidt gradient identities.

The registered declaration is the fieldwise transport of the proved
`NSFormalization.Section3.T13.localizationAPI`; it is not a theorem whose
premise assumes a `LocalizationAPI`.

## 2. What Lean now contains

The public contract, binding, and test are:

- `verification/Contracts/V1/Localization.lean`;
- `verification/Bindings/Localization.lean`; and
- `verification/Tests/Localization.lean`.

The contract restates ten T13 definitions and the six-field API token-for-token
from `research/T13/Spec.lean`, while importing the registered T01 periodic data
and D01 whole-space homogeneous norm.  The eleventh vocabulary definition,
`latticeVector`, was already declared at the required root namespace by the
frozen `T02.local_potential` V1 contract.  Redeclaring it made the two contracts
impossible to import together, so Localization reuses it and checks by `rfl`
that it is the canonical T13 lattice vector.  The permanent
`research/T13/probes/contract_coimport.lean` probe verifies both T02 bindings
can be imported jointly.

All eleven vocabulary definitions have whole-function `rfl` drift guards; no
pointwise bridge is needed.  The binding also checks the registered D01 norm by
`rfl` and constructs the contract record field by field from the canonical
proved record.  Tests provide `checkedLocalization`, the transitive axiom
check, one independent Spec-conformance example for each field, and the
`s=1/2` localization estimate on an explicitly proved nonzero `ContDiffBump`
field supported in an admissible ball.

The registry now has 42 contracts.  Its scope records the implementation's
explicit witness
`(1 + (4 · tailGeomConst s c r / cFrac s) ^ (1/2)).toReal` for the contract's
uniform existential constant.  The T13 ledger is claimed by `erenup` and lists
`T02.localization`.

## 3. Remaining gap and exclusions

No T13 proof gap remains for the six registered fields.  This contract does
not expose the internal lattice-tail bound or periodization-uniqueness lemma,
does not add a divergence-free hypothesis or conclusion, and does not assert a
fractional localization estimate at or outside the range `0 < s < 1`.

The only registration-level accommodation is reuse of the frozen
`Contracts.V1.latticeVector` described above.  It changes neither the Spec
statement nor any field type: the co-import probe and the T13 bridge both close
by definitional equality.

## 4. Commands and results

Lean environment: `. scripts/lean-env.sh`; Lake commands were run from
`verification/` with `LEAN_NUM_THREADS=6`.

The focused build succeeded:

```text
$ lake build Contracts.V1.Localization Bindings.Localization Tests.Localization
Built Contracts.V1.Localization
Built Bindings.Localization
Built Tests.Localization
Contract BlowupDensity.Tests.checkedLocalization: checked; standard logical axioms only
```

The co-import probe and contract axiom audit both elaborate.  The axiom file
prints the same result for every bridge, the transported API, and the checked
declaration; the final two lines are:

```text
'BlowupDensity.Bindings.localizationAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedLocalization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The required full gate passed:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh
== make check
45 work items: ownership, contract registration and task cards consistent.
== make test
Contract BlowupDensity.Tests.checkedLocalization: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
== gates OK
```

The explicit base-aware registry check exited 0:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
  "registered_contracts": 42,
  "base_compatibility_checked": true,
```

The registry is canonical UTF-8 JSON (`ensure_ascii=False`, `indent=2`) and its
diff is append-only:

```text
$ git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
$ git diff --numstat verification/contracts.json
11      0       verification/contracts.json
```
