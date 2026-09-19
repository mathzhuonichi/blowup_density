REJECT

## 1. What the lane claims

The continuation of `research/T17/REPORT_453.md` claims a complete 45-field
assembly at the concrete `correctionData`, a proof of
`correctionStatementAmended_holds`, a registered raw-field contract
`T02.correction`, and a cube-centred non-vacuity witness with a nonzero constant
reference.  It explicitly says that its final hypothesis block includes

```lean
Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius
```

(`research/T17/REPORT_453.md:82-86`).  The registry repeats that premise in its
scope (`verification/contracts.json:511-518`).  The report also says that the
packet-indexed `CorrectionAPI` and unamended `correctionStatement` are copied
byte-for-byte from the reconciled Spec, while the registered theorem uses a
fieldwise-equivalent raw-field record.

The paper content cited by the lane is present: `lem:correction` defines the
force and states support, derivative, energy, mixed, and Sobolev bounds at
`paper/sections/03-torus.tex:218-242`, with the profile and scaling calculation
at `paper/sections/03-torus.tex:245-284`.  The preceding construction chooses
`x₀ ∈ B` and a small scale at `paper/sections/03-torus.tex:101-105`, while the
local potential is made in a ball centred at `x₀` at
`paper/sections/03-torus.tex:176-188`.

## 2. What is in Lean

The implementation quality is otherwise good.

- The canonical, raw-contract, and packet-contract `CorrectionAPI` structures
  each have 45 fields.  The canonical fields occupy
  `formalization/NSFormalization/Section3/T17/Correction.lean:71-281`; the raw
  contract is at `verification/Contracts/V1/Correction3.lean:208-418`; the
  packet spelling is at `verification/Contracts/V1/Correction3.lean:524-732`.
  Exact `diff` comparisons of Spec lines 752-960 against contract lines
  524-732, and Spec lines 980-985 against contract lines 752-757, produced no
  output.  Thus the packet structure and unamended statement are genuinely
  byte-identical.

- `correctionAPI_of_smooth` fills every field at the concrete data
  (`formalization/NSFormalization/Section3/T17/Assembly.lean:35-103`).  It uses
  T13's actual `localizationAPI`
  (`formalization/NSFormalization/Section3/T13/Assembly.lean:328-336`) and T16's
  actual local-potential constructor
  (`formalization/NSFormalization/Section3/T16/Assembly.lean:423-478`).  The
  threshold is honestly shrunk to `min ε₁ place.ε₀`, remains positive, and is
  passed to the concrete record (`Assembly.lean:112-126`); this agrees with the
  positive threshold lemma at
  `formalization/NSFormalization/Section3/T16/LocalPotential.lean:262-267`.

- The paper rates are represented with the correct exponents and guards.  In
  particular, the mixed constant is selected from a finite ENNReal witness
  (`formalization/NSFormalization/Paper1/CorrectionMixedNorms.lean:123-134`),
  and the proof uses that witness's `ne_top` before `ofReal_toReal`
  (`formalization/NSFormalization/Section3/T17/Mixed.lean:83-86`).  There is no
  hidden `⊤.toReal = 0` argument.

- The non-vacuity theorem supplies `reference ≠ 0`, `0 < D.ε₀`, an actual
  element `D.ε₀ ∈ Ioc 0 D.ε₀`, and a full API
  (`formalization/NSFormalization/Section3/T17/Assembly.lean:167-187`).  Hence
  the scale interval is not empty.  Positivity of `place.T`, `δ`, and `r` also
  makes the theorem's main time/space domains genuine.

- The contract bridges restated functions by `rfl`
  (`verification/Bindings/Correction3.lean:119-141`), converts the two record
  types fieldwise (`verification/Bindings/Correction3.lean:143-245`), and proves
  both round trips (`verification/Bindings/Correction3.lean:247-257`).  Tests
  exercise the registered theorem, three exact Spec fields, and non-vacuity
  (`verification/Tests/Correction3.lean:16-69`).

- All changed Lean modules are new files; the only modified tracked files are
  records/docs/registry.  The changed Lean sources and reviewer probe contain no
  `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats`.  Every printed
  declaration in `axioms_u12.lean` has exactly
  `[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and findings

1. **Blocking — statement fidelity (`correctionStatementAmended`).**  The binding
   G4 statement in the review brief ends after the raw packet-support premise
   and then concludes `∃ D, ...`; it does **not** assume ball-in-chart.  The Lean
   definition adds exactly that extra premise at
   `formalization/NSFormalization/Section3/T17/Assembly.lean:21-31`.  It is copied
   into the contract at `verification/Contracts/V1/Correction3.lean:429-439`,
   required by the acceptance test at `verification/Tests/Correction3.lean:23-32`,
   and advertised by the registry at `verification/contracts.json:518`.

   This is not derivable from placement.  Placement only says that the centre
   lies in the chart ball
   (`formalization/NSFormalization/Section3/T15/Scaling.lean:135-142`); it places
   no upper bound on the independently quantified `r`.  The assembly consumes
   `hball` directly as the API's `ball_in_chart` field and to derive the cube
   premise (`formalization/NSFormalization/Section3/T17/Assembly.lean:40,56-64`).
   Thus the additional premise is load-bearing, not a redundant spelling.

   More decisively, the lane's own research probe defines the brief's exact G4
   proposition at
   `research/T17/probes/assembly_geometry_obstruction_module.lean:68-78` and
   proves its negation at lines 80-88, using a chart radius `1/8` and requested
   radius `1/4`.  That probe compiles with only the standard three axioms.  The
   current branch therefore proves a mathematically sensible **different**
   theorem, while the required theorem is kernel-refuted.

   **Required fix:** this is not a one-line Lean repair.  If the supplied brief
   remains authoritative, remove/disable the completed registration and return
   U12 to blocked status with `statedG4_false` as the reason.  If the intended
   ruling is instead the later ball-in-chart version recorded by the worker,
   the authoritative lane brief must first be amended explicitly; then this
   implementation can be re-reviewed against that statement.

2. **Passed — substantive negative mutation.**  The reviewer probe
   `research/T17/probes/rev453_widen_radius.lean:15-30` widens the main guard
   from `r < 1/2` to `r < 3/4` without deleting an argument.  Reusing the proof
   fails exactly because `r < 3/4` cannot fill `r < 1/2`; exact error is in §4.

3. **Passed — gap/tree audit.**  The continuation report declares no remaining
   missing Section 4 lemma.  For the earlier geometry gap, a whole-tree search
   for `ball_in_chart|statedG4|correctionStatementAmended|chartBall_in_cube|GeometryObstruction`
   in `formalization/NSFormalization/Section4` produced no output.  In any case,
   the explicit counterexample proves that no lemma can derive the missing
   inclusion from the supplied premises.

## 4. Commands and results

All Lake commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`.  The unfiltered `make check` and `scripts/gates.sh`
commands both exited 0.  They print a greater-than-1-MiB contract-closure JSON;
the exact verdict-bearing output from concise reruns is pasted below.

Module build and direct elaboration:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Assembly 2>&1 | rg 'Section3/T17/Assembly|NSFormalization.Section3.T17.Assembly|Build completed'
Build completed successfully (10032 jobs).

$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T17/Assembly.lean
[no output; exit 0]
```

The unfiltered build additionally replayed warnings from existing imported
modules, but emitted no warning from `Section3/T17/Assembly.lean` itself.
`lake build Bindings.Correction3 Tests.Correction3` exited 0 and ended with:

```text
ℹ [10051/10051] Replayed Tests.Correction3
info: Tests/Correction3.lean:20:0: Contract BlowupDensity.Tests.checkedCorrection3: checked; standard logical axioms only
info: Tests/Correction3.lean:69:0: Contract BlowupDensity.Tests.checkedCorrection3_nonvacuous: checked; standard logical axioms only
Build completed successfully (10051 jobs).
```

Axiom audit (`lake env lean ../research/T17/axioms_u12.lean`, exit 0):

```text
'NSFormalization.Section3.T17.correctionAPI_of_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionStatementAmended_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.chart_in_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.place' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.reference_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Nonvacuity.nonvacuous_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.ofContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.toContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.ofPacket' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.toPacket' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.correctionStatement_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Correction3.correctionStatementAmended_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.Packet.correctionStatement_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.correctionStatementAmended_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Correction3.nonvacuous_correction' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCorrection3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCorrection3_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Bindings.Correction3.to_of: checked; standard logical axioms only
Contract BlowupDensity.Bindings.Correction3.of_to: checked; standard logical axioms only
Contract BlowupDensity.Bindings.Correction3.toPacket_ofPacket: checked; standard logical axioms only
Contract BlowupDensity.Bindings.Correction3.ofPacket_toPacket: checked; standard logical axioms only
```

The mathematical reproducer for the fidelity failure
(`lake env lean ../research/T17/probes/assembly_geometry_obstruction_module.lean`,
exit 0) prints:

```text
'NSFormalization.Section3.T17.GeometryObstruction.chart_in_cube' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.place' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.ball_not_in_chart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.statedG4_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.GeometryObstruction.reference_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Substantive radius mutation (`lake env lean
../research/T17/probes/rev453_widen_radius.lean`, expected exit 1):

```text
../research/T17/probes/rev453_widen_radius.lean:30:10: error: Application type mismatch: The argument
  hr34
has type
  r < 3 / 4
but is expected to have type
  r < 1 / 2
in the application
  correctionStatementAmended_holds ν u p f K place v r δ hν hr hr34
```

`make check` concise exact rerun
(`make check 2>&1 | rg '"source_hashes_match"|"registered_contracts"|"base_compatibility_checked"|Ran 13 tests|^OK$|work items:'`,
exit 0):

```text
  "source_hashes_match": false
  "registered_contracts": 47,
  "base_compatibility_checked": false,
Ran 13 tests in 0.047s
OK
45 work items: ownership, contract registration and task cards consistent.
```

`source_hashes_match: false` is the repository's reported copied-source snapshot
state and is non-fatal; no copied source is modified by this lane.

`BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh`
was also rerun through
`rg '^==|Correction3|extra_axiom|weakened_hypothesis|Mutation suite|"base_compatibility_checked"'`;
the filtered pipeline exited 0 with this exact output:

```text
== make check
      "Bindings.Correction3",
      "Contracts.V1.Correction3",
      "Tests.Correction3"
  "base_compatibility_checked": false,
== make test
info: Tests/Correction3.lean:20:0: Contract BlowupDensity.Tests.checkedCorrection3: checked; standard logical axioms only
info: Tests/Correction3.lean:69:0: Contract BlowupDensity.Tests.checkedCorrection3_nonvacuous: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
== gates OK
```

Base-aware contract check (exit 0), with base count checked separately as 46:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3 | rg '"registered_contracts"|"base_compatibility_checked"'
  "registered_contracts": 47,
  "base_compatibility_checked": true,

$ git show origin/erenup/integration-section3:verification/contracts.json | jq '.contracts | length'
46
```

Hygiene and registry diff:

```text
$ git diff --check origin/erenup/integration-section3...HEAD
[no output; exit 0]

$ rg forbidden-token/maxHeartbeats patterns over every changed Lean file and rev453 probe
[no output; exit 1 because there were no matches]

$ git diff --stat verification/contracts.json
[no output; exit 0: the lane changes are committed]

$ git diff --stat origin/erenup/integration-section3...HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --name-status origin/erenup/integration-section3...HEAD` shows every
changed `.lean` file as `A`; the `M` entries are only markdown/JSON/generated
records.  No existing Lean module was modified.
