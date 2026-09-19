ACCEPT

# Review of lane 455-T18-U12-assembly-registration

## 1. What the lane claims

The worker claims that `NSFormalization.Section3.T18.assemble` packages all 45
fields of the reconciled insertion record, with only the three intentional raw
premises `hsupp`, `hM`, and `hD`; that the registered statement adds none of
those premises; and that concrete end-to-end inhabitation remains staged
(`research/T18/REPORT_455.md:5-19`, `research/T18/REPORT_455.md:54-71`). Those
claims are accurate.

Statement fidelity checks:

- The paper asks for exact lifespan and blow-up, the quiet history through
  `T-2ε²`, divergence-free `O(ε)` support, the energy/mixed/Sobolev rates, and
  negative-order convergence (`paper/sections/03-torus.tex:287-310`); its proof
  defines the inserted triple and the two vanishing cross terms and derives
  exact momentum and lifespan (`paper/sections/03-torus.tex:312-345`). The
  registered record contains those same clauses: formulas at
  `verification/Contracts/V1/PeriodicInsertion.lean:575-602`, dynamics and
  history at `:606-652`, lifespan/blow-up at `:661-694`, cross terms and support
  at `:703-749`, and the three rates plus honesty fields at `:757-833`.
- A literal `diff -u` of `research/T18/Spec.lean:1658-1988` against
  `verification/Contracts/V1/PeriodicInsertion.lean:523-853` has no output.
  Thus both `PeriodicInsertionAPI` and `periodicInsertionStatement` are copied
  token-for-token. The statement's parameter order is visibly identical at
  `research/T18/Spec.lean:1977-1987` and
  `verification/Contracts/V1/PeriodicInsertion.lean:842-852`.
- An independent field count gives 45 in both structures. The canonical fields
  are `formalization/NSFormalization/Section3/T18/Assembly.lean:20-169`; the
  contract fields are `verification/Contracts/V1/PeriodicInsertion.lean:536-833`.
- The T15 `ScalingAPI` structure itself is also literal: comparing
  `research/T18/Spec.lean:548-803` with
  `verification/Contracts/V1/PeriodicInsertion.lean:199-454` has no substantive
  difference. Registered placement and correction vocabulary is reused by the
  exports at `verification/Contracts/V1/PeriodicInsertion.lean:190` and
  `:462-467`, rather than duplicated.
- The canonical constructor assigns every field to the corresponding U1-U11
  declaration (`formalization/NSFormalization/Section3/T18/Assembly.lean:178-223`).
  Spot checks against the cited tree declarations confirm the exact types:
  cross transport at `CrossTransport.lean:82,90`, momentum at
  `Momentum.lean:110`, the explicit support-premise theorem at
  `Support.lean:175-182`, solution/lifespan/maximality at
  `Lifespan.lean:167-170,300-303,338-340`, energy at
  `EnergyRate.lean:262-267`, mixed rate at `MixedRate.lean:154-166,186-191`,
  and Sobolev/tail fields at `SobolevRate.lean:201-232,303-337`.

No vacuity escape was found:

- The common threshold has `eps_pos : 0 < ε₀`, and every scale-dependent field
  is guarded by `Ioc 0 ε₀` (`Assembly.lean:26-32,53-169`). The reviewer witness
  `ε=ε₀` proves this interval is nonempty
  (`research/T18/probes/rev455_nonvacuity.lean:9-19`).
- The support radius is strictly positive (`Assembly.lean:114-125`), while the
  actual theorem consumes the raw packet support clause rather than a named
  opaque proposition (`Support.lean:169-195`).
- `hM` and `hD` are used precisely where `ENNReal.ofReal` requires sign
  information (`EnergyRate.lean:257-279`). At the binding boundary they are
  derived from the packet's exact `IsLUB` and dissipation equality
  (`verification/Bindings/PeriodicInsertion.lean:183-194`), whose source fields
  are `verification/Contracts/V1/Packet.lean:255-267`.
- The mixed `toReal` is not allowed to collapse `⊤` to zero: the proof first
  establishes `N ≠ ⊤` from an honest mixed path
  (`formalization/NSFormalization/Section3/T18/MixedRate.lean:196-207`) and only
  then uses `ENNReal.ofReal_toReal` (`:220-229`). The mixed and Sobolev record
  conclusions also retain their explicit path-membership guards
  (`Assembly.lean:137-169`).
- The outer `0 < ν` is mathematically faithful to the paper. It is redundant
  after a `CorrectionAPI` parameter is supplied, because that record itself
  contains `viscosity_pos : 0 < ν`
  (`verification/Contracts/V1/Correction3.lean:208-237`); this is not an added
  hypothesis or an empty-domain device.

## 2. What is in Lean

The canonical statement quantifies the raw packet fields and all threaded
records, exposes `RawPremises`, and returns a nonempty 45-field record
(`formalization/NSFormalization/Section3/T18/Assembly.lean:171-240`). The
canonical conditional non-vacuity theorem is at `:242-248`.

The binding is a genuine fieldwise assembly:

- raw registered inputs are converted at
  `verification/Bindings/PeriodicInsertion.lean:20-181`;
- all 45 fields are transported in both directions at `:197-327`, with `rfl`
  round trips at `:329-345`;
- `periodicInsertion` builds `RawPremises` from `P.velocity_support`, the LUB
  sign proof, and the dissipation sign proof at `:347-358`;
- the exact registered existence statement closes at `:360-362`;
- all restated definitions have named `rfl` bridges at `:365-405`;
- placement/scaling/correction inverse adapters are at `:407-525`;
- the requested staged witness theorem is at `:527-543`, and the statement
  equivalence is at `:545-563`.

The test checks the registered statement and its axioms
(`verification/Tests/PeriodicInsertion.lean:11-15`), independently checks the
momentum/support/energy shapes (`:17-42`), and checks the staged witness theorem
(`:46-59`). Registry entry `T03.periodic_insertion`, version 1 and parent `T02`,
is at `verification/contracts.json:532-541`; the work item names that same
contract and parent deliverable at `collaboration/work_items.json:380-387`.

Negative and non-vacuity review probes:

- `research/T18/probes/rev455_nonvacuity.lean:9-19` compiles with zero output
  and exhibits an admissible scale for every API witness. The already registered
  T17 prerequisite also has a concrete nonzero-reference full correction
  witness at `verification/Tests/Correction3.lean:59-69`.
- `research/T18/probes/rev455_mutation.lean:22-27` substantively widens the
  history interval from `t ≤ T-2ε²` to `t ≤ T-ε²`. Applying `.history` fails
  with the expected premise mismatch; no argument was dropped.

Hygiene passes. No lane Lean deliverable contains `sorry`, `admit`, an `axiom`
declaration, `native_decide`, or `set_option maxHeartbeats`. Direct elaboration
of the assembly has no warnings or output from that module. The requested
three-dot name-status check emits a criss-cross merge-base warning, but no Lean
path has status `M`. The eight prerequisite recovery files described at
`research/T18/REPORT_455.md:40-48` compare byte-for-byte with base commit
`33515e1fea080d094f2b97863a843317e259480e`; only the T18 assembly/registration
is new over that base.

## 3. Gaps

There is no proof, statement, axiom, policy, or build gap in lane 455.

The one deliberately staged item is a concrete end-to-end `PeriodicInsertionAPI`
witness. T17 already supplies a correction existence theorem and a concrete
nonzero example (`formalization/NSFormalization/Section3/T17/Assembly.lean:175-187`),
but the current T15 tree only defines `scalingStatement`; it does not prove a
`scalingStatement_holds` theorem
(`formalization/NSFormalization/Section3/T15/Scaling.lean:456-501`). Thus a full
T15 U15 scaling/placement witness compatible with the chosen reference and
correction data remains the honest gate, exactly as recorded in
`research/T18/T18_SPLIT.md:247-265` and `research/T18/ATTEMPTS_U12.md:74-86`.

As required, the whole Section4 tree was searched for every relevant missing
witness name:

```text
$ grep -rn -E 'NSFormalization\.Section3\.T15\.ScalingAPI|BlowupDensity\.T15\.Draft\.ScalingAPI|PeriodicInsertionAPI|periodicInsertionStatement|NSFormalization\.Section3\.T17\.CorrectionAPI|BlowupDensity\.T17\.Spec\.CorrectionAPI|correctionStatementAmended' formalization/NSFormalization/Section4
[no output]
```

Generic Section4/R42 records named `ScalingAPI` or `CorrectionAPI` are the
whole-space construction and do not inhabit the parameterized T15/T17 records.
No fix is required in lane 455.

## 4. Commands and results

All Lean/Lake commands were run after `. scripts/lean-env.sh`, from
`verification/`, with `LEAN_NUM_THREADS=6`. Lake processes were run one at a
time.

### Target builds

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.Assembly
[replayed dependency warnings only; no Assembly warning]
Build completed successfully (10618 jobs).
exit 0

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T18/Assembly.lean
[0 output]
exit 0

$ LEAN_NUM_THREADS=6 lake build Tests.PeriodicInsertion
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
Build completed successfully (10664 jobs).
exit 0
```

The build replayed warnings only from pre-existing dependencies (for example
`Source.FiniteHilbertBochner`, `Paper1.PeriodicSobolevHilbert`, and vendor
`Formal.EndpointSafeTwoSpacePicard`); it printed no warning from Assembly,
Bindings, Contract, or Test lines.

### Axiom audit

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T18/axioms_u12.lean
exit 0
$ diff -u <(LEAN_NUM_THREADS=6 lake env lean ../research/T18/axioms_u12.lean) <(sed -n '121,252p' ../research/T18/REPORT_455.md)
axiom_report_diff_exit=0
$ # independent count of the same output
78
     78 Classical.choice
     78 Quot.sound
     78 propext
```

The complete exact output is already pasted at
`research/T18/REPORT_455.md:121-252`; the zero diff above confirms the reviewer
rerun reproduced it byte-for-byte. Every one of the 78 prints is exactly
`[propext, Classical.choice, Quot.sound]`.

### Architecture, tests, mutations, and base compatibility

`make check` exited 0. Its exact decisive output was:

```text
  "registered_contracts": 49,
  "base_compatibility_checked": false,
Ran 13 tests in 0.048s

OK
45 work items: ownership, contract registration and task cards consistent.
```

`base_compatibility_checked: false` is expected for the unparameterized check;
the required base-aware invocation below reports true. The plan checker also
reports the repository's pre-existing `source_hashes_match: false` and the
known copied `BoundaryCorollary.lean` token while exiting 0.

The full `scripts/gates.sh` output was 57,672 lines / 2,392,369 bytes (SHA-256
`df7e729657201ad810c724aa4980aa15690745d78955717b706d8e668773260e`).
Its exact final output was:

```text
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
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

Command and result:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh
gates_exit=0
```

The explicit base-aware check produced 57,575 lines / 2,383,960 bytes
(SHA-256 `9de4fbb2993d37e21c1b844012df3392b0a281ea07376e1004d4a23b3ac84b7e`):

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
check_contracts_exit=0
{
  "registered_contracts": 49,
  ...
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The omitted middle value is only the 57,570-line module-closure object. Counts
were checked independently:

```text
$ jq '.contracts | length' verification/contracts.json
49
$ git show origin/erenup/integration-section3:verification/contracts.json | jq '.contracts | length'
48
```

### Mutation and non-vacuity probes

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T18/probes/rev455_nonvacuity.lean
[0 output]
nonvacuity_exit=0

$ LEAN_NUM_THREADS=6 lake env lean ../research/T18/probes/rev455_mutation.lean
../research/T18/probes/rev455_mutation.lean:27:2: error: Type mismatch
  A.history
has type
  ∀ ε ∈ Ioc 0 A.ε₀,
    ∀ (t : ℝ), 0 ≤ t → t ≤ place.T - 2 * ε ^ 2 → ∀ (x : Space), A.velocity ε (t, x) = reference.velocity (t, x)
but is expected to have type
  ∀ ε ∈ Ioc 0 A.ε₀,
    ∀ (t : ℝ), 0 ≤ t → t ≤ place.T - ε ^ 2 → ∀ (x : Space), A.velocity ε (t, x) = reference.velocity (t, x)
mutation_exit=1
```

### Hygiene and registry diff

```text
$ rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom\b' <changed Lean files>
[no matches]
$ rg -n 'set_option\s+maxHeartbeats' <changed Lean files>
[no matches]
$ git diff --check
[0 output]

$ git diff --name-status origin/erenup/integration-section3...HEAD | awk '$1 == "M" && $2 ~ /\.lean$/ {print}'
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using e5629476ac4b0e5684e83c2d01fd8e56d032047a
[no Lean path]
```

The exact requested registry-stat commands give:

```text
$ git diff --stat verification/contracts.json
[0 output: the lane is committed]

$ git diff --stat origin/erenup/integration-section3...HEAD -- verification/contracts.json
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using e5629476ac4b0e5684e83c2d01fd8e56d032047a
 verification/contracts.json | 33 +++++++++++++++++++++++++++++++++
 1 file changed, 33 insertions(+)

$ git diff --stat 33515e1fea080d094f2b97863a843317e259480e..HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

The first 22 lines in the three-dot result are the two already-landed recovered
prerequisite entries. Against the base commit cited by the worker and used for
the byte comparisons, lane 455 adds exactly the one 11-line T18 registration.

Fixes: none.
