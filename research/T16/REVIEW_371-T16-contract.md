REJECT

## 1. What the lane claims

The worker report claims registration of `T02.local_potential` V1 with four
helper definitions, a seven-field `CutoffData`, a 26-field
`LocalPotentialAPI`, fieldwise transport from the canonical assembly theorem,
an axiom audit, and a zero-field witness
(`research/T16/REPORT_371.md:3-7`).  It also explicitly says that the full
repository gates had not been run (`research/T16/REPORT_371.md:9`).

The registry makes the corresponding enabled claim under parent `T02`, names
the contract/binding/test/declaration, records all seven `correction_*` clauses,
the structure exception, and excludes the T17 correction bound
(`verification/contracts.json:445-453`).

## 2. What is in Lean

### Statement fidelity

The core registered statement is faithful.

* The four helper bodies, the two structures, and
  `localPotentialStatement` in `verification/Contracts/V1/LocalPotential.lean`
  are token-identical to the portion of `research/T16/Spec.lean` beginning at
  `latticeVector`, modulo namespace/import changes.  A comment/whitespace
  stripped comparison returned `equal=True` with SHA-256
  `8f941f7c7263bf1eaa0c06b052b3b4fdb9acd1a61d45668fd188608c264d3678`
  on both sides.  The helpers occur at
  `verification/Contracts/V1/LocalPotential.lean:27-55`, the seven data fields
  at `:65-105`, the 26 API fields at `:114-288`, and the theorem statement at
  `:297-305`.
* The reused `PeriodicFrequency` and `IsPeriodicOn` have the intended
  statements in the already registered torus vocabulary
  (`verification/Contracts/V1/TorusData.lean:38-40,58-62`).
* The mathematical content matches the manuscript: the radial potential and
  curl identity are at `paper/sections/03-torus.tex:176-181`, the cutoff formula
  at `:182-187`, smoothness/divergence/support at `:188-189`, cancellation at
  `:190-193`, and the proof's smallness, periodic extension, and active interval
  at `:212-215`.  The contract's `Ioc (0,D.ε₀)`, `Ioo` support, `Ico
  (T-ε²) T`, local chart smoothness, and absence of a correction norm bound are
  consistent with those lines and the reconciled Spec.
* The four drift bridges are genuine whole-function `rfl` equalities
  (`verification/Bindings/LocalPotential.lean:9-12`).  `CutoffData` has both
  fieldwise conversions and both round trips (`:14-19`).  `api_toContract`
  explicitly transports all 26 fields (`:21-26`), and the registered theorem
  obtains its witness from the canonical theorem rather than from a hypothesis
  (`:28-31`).  The source theorem itself is
  `NSFormalization.Section3.T16.localPotential : localPotentialStatement`
  (`formalization/NSFormalization/Section3/T16/Assembly.lean:480-492`).
* The named hypotheses are not vacuous or decorative.  In the canonical
  constructor, `r < 1/2`, compactness, periodicity, local smoothness,
  divergence-freeness, and packet support all feed the correction construction
  (`formalization/NSFormalization/Section3/T16/Assembly.lean:423-450`), while
  `r,T,δ>0` choose a positive common threshold (`:483-492`).  There is no
  `⊤.toReal`, empty-interval trick, or unused theorem binder in this statement.
* Reviewer probe `research/T16/probes/rev371_nonvacuity.lean:13-34` applies the
  registered binding at `r=1/4`, `T=δ=1`, `K={0}`, and the genuinely nonzero
  constant periodic divergence-free field `v=e₀`; it typechecks with no output.
  Thus the theorem itself is substantively satisfiable.

The registry entry is append-only: the base-relative stat is exactly

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

No pre-existing Lean module was modified.  The exact base diff for Lean files
is:

```text
A research/T16/axioms_contract.lean
A verification/Bindings/LocalPotential.lean
A verification/Contracts/V1/LocalPotential.lean
A verification/Tests/LocalPotential.lean
```

### Hygiene

The exact search

```text
rg -n '\b(sorry|admit|axiom|native_decide)\b' \
  verification/Contracts/V1/LocalPotential.lean \
  verification/Bindings/LocalPotential.lean \
  verification/Tests/LocalPotential.lean research/T16/axioms_contract.lean
```

had no output.  The `maxHeartbeats` search also had no output.  `git diff
--check origin/erenup/integration-section3...HEAD` and JSON parsing both exit
zero.

## 3. Gaps

1. **Blocking — the required Spec conformance example is absent.**
   `verification/Tests/LocalPotential.lean:11` merely proves
   `Contracts.V1.localPotentialStatement` from `checkedLocalPotential`; it does
   not independently restate the quantifiers/fields from
   `research/T16/Spec.lean:328-336`.  Consequently the test would not detect a
   coordinated drift of the contract and binding.  Replace this self-reference
   with an independently written conformance example matching the Spec.

2. **Blocking — the required nonzero test was replaced by a zero example.**
   `verification/Tests/LocalPotential.lean:12-17` uses `v=0`, `U=0` and invokes
   `localPotential_zero`.  The brief expressly required a nonzero constant
   divergence-free reference as in `assembly_closes.lean`.  The reviewer probe
   at `research/T16/probes/rev371_nonvacuity.lean:13-34` demonstrates the exact
   replacement and compiles cleanly; move an equivalent example into the test.

3. **Blocking record fix — the submitted report does not contain the mandated
   gate outputs and incorrectly leaves them outstanding.**  The reviewer ran
   all gates successfully below.  Update `research/T16/REPORT_371.md:9` with the
   actual commands/results and retain the required four-part report structure.

4. **Record accuracy — `ATTEMPTS_CONTRACT.md` calls the bridges “pointwise”.**
   The four declarations are whole-function equalities (`Bindings` lines
   9-12); change `research/T16/ATTEMPTS_CONTRACT.md:3` to say “whole-function
   `rfl` bridges”.

The report's only stated scope gap is the correction norm bound assigned to
T17 (`research/T16/REPORT_371.md:7`).  A whole-tree search of
`formalization/NSFormalization/Section4` found related implementation results,
including the two energy halves documented at
`Section4/I02/Energy.lean:8-25` and a correction-force component norm theorem at
`Section4/I03/HomogeneousScaling.lean:172-187`.  Therefore I interpret the
report honestly as “not asserted by this T16 contract / packaged by T17”, not
as “no related lemma exists in the tree.”  Searches for the T16-specific names
`potential_smooth`, `potential_curl`, `correction_periodic`,
`correction_support_ball`, `correction_cancels`, and
`localPotentialStatement` in the entire Section4 tree returned no matches.

## 4. Commands and results

Environment for every Lean command:

```text
. scripts/lean-env.sh
export LEAN_NUM_THREADS=6
```

All `lake` commands were run from `verification/`.

1. `lake build Contracts.V1.LocalPotential`

```text
Build completed successfully (8820 jobs).
```

The replay printed only pre-existing warnings from imported modules; it printed
no warning from `Contracts/V1/LocalPotential.lean`.

2. `lake env lean Contracts/V1/LocalPotential.lean`

```text
(no output; exit 0)
```

3. `lake build Bindings.LocalPotential`

```text
Build completed successfully (9368 jobs).
```

4. `lake build Tests.LocalPotential`

```text
info: Tests/LocalPotential.lean:10:0: Contract BlowupDensity.Tests.checkedLocalPotential: checked; standard logical axioms only
Build completed successfully (9370 jobs).
```

5. `lake env lean ../research/T16/axioms_contract.lean`

```text
'BlowupDensity.Tests.checkedLocalPotential' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is the only `#print axioms` in the submitted axiom file, and its list is
exactly the required list.

6. `BASE_REF=origin/erenup/integration-section3 make check`

```text
"registered_contracts": 41,
"base_compatibility_checked": false,
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
45 work items: ownership, contract registration and task cards consistent.
```

Exit status: `0`.  (`make check` invokes `check_contracts.py` without a base,
so its `base_compatibility_checked` value is correctly `false`; the required
base-aware invocation below is `true`.)

7. `BASE_REF=origin/erenup/integration-section3 scripts/gates.sh`

```text
== make check
45 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/LocalPotential.lean:10:0: Contract BlowupDensity.Tests.checkedLocalPotential: checked; standard logical axioms only
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

Exit status: `0`.

8. `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`

```text
"registered_contracts": 41,
"base_compatibility_checked": true,
"scope": "Architecture checks only; run lake test for Lean type and axiom checks."
```

Exit status: `0`.

9. Substantive negative mutation:
   `lake env lean ../research/T16/probes/rev371_mutation.lean`.  The probe widens
   the chart guard from `r < 1/2` to `r < 1` at
   `research/T16/probes/rev371_mutation.lean:12-25`.  It fails for the expected
   reason:

```text
../research/T16/probes/rev371_mutation.lean:25:50: error: Application type mismatch: The argument
  hr1
has type
  r < 1
but is expected to have type
  r < 1 / 2
in the application
  Bindings.localPotential v U K x₀ r T δ hr hr1
```

10. Non-vacuity probe:
    `lake env lean ../research/T16/probes/rev371_nonvacuity.lean`

```text
(no output; exit 0)
```

The mathematical registration and transport are sound, but the submitted test
and records do not satisfy the lane's explicit acceptance requirements.  Fix
the four items above and rerun the same commands.

## 5. Fix applied (continuation)

The four requested record and test fixes are now applied. `Tests/LocalPotential.lean`
contains an independent Spec-shaped statement and a checked equivalence listing
all 26 `LocalPotentialAPI` fields, plus the verified nonzero constant field
instance (`coordinateVector 0`, `U = 0`, `K = {0}`, `r = 1/4`, `T = δ = 1`) and
the proof that `coordinateVector 0 ≠ 0`. `REPORT_371.md` now records the full
base-aware gates, axiom output, and append-only registry stat;
`ATTEMPTS_CONTRACT.md` says “whole-function `rfl` bridges”; and both reviewer
probes are retained in the fix commit. The rerun of
`BASE_REF=origin/erenup/integration-section3 scripts/gates.sh` and the explicit
base-aware `check_contracts.py` command exited 0 with 41 registered contracts
and `base_compatibility_checked: true`.
