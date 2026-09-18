ACCEPT-WITH-NOTES

Exact one-line fix required before merge: in `research/T11/REPORT_340.md:7`, replace
`` `appendix-a-local-theory.tex:60-158` `` with
`` `paper/sections/appendix-a-local-theory.tex:60-157` ``.  The cited file is
under `paper/sections/` and ends at line 157.  This is a citation-only correction;
I found no mathematical, Lean, contract, axiom, or gate defect.

## 1. What the lane claims

The worker report claims four assembled APIs: the eight-field local theory, the
five-field continuation API with its two restart balls explicitly narrowed from
manuscript `H¹` to proved `H³`, the six-field Galilean mean reduction, and the
four-field viscosity rescaling (`research/T11/REPORT_340.md:5-37`).  It also
claims that the manuscript-strength continuation package follows from exactly
the two named, unproved predicates `PeriodicRestartH1` and
`PeriodicRestartBeyondH1` (`research/T11/REPORT_340.md:65-70`).

These are faithful to the cited mathematics.  Proposition `prop:local` states
existence, uniqueness, maximal lifespan and the finite squared-`H²`
continuation criterion at `paper/sections/02-preliminaries.tex:105-118`.
The appendix supplies common-interval regularity at
`paper/sections/appendix-a-local-theory.tex:60-77`, viscosity rescaling at
`:79-87`, the mean/Galilean transform at `:89-106`, maximal gluing and
uniqueness at `:117-125`, and the higher-order/restart argument at `:127-156`.
The latter really says `H¹` at `:147-150`; the lane does not silently relabel
that manuscript claim as proved.

Field-for-field comparison is exact:

- `PeriodicLocalTheoryAPI` in the reconciled spec
  (`research/T11/Spec.lean:571-670`) is reproduced in Assembly
  (`formalization/NSFormalization/Section3/T11/Assembly.lean:118-181`) and in
  the contract (`verification/Contracts/V1/TorusLocalTheory.lean:437-517`).
- The manuscript continuation structure is the spec's five fields
  (`research/T11/Spec.lean:677-766`) at
  `formalization/NSFormalization/Section3/T11/Assembly.lean:202-262`.  The
  registered structure at `formalization/NSFormalization/Section3/T11/Assembly.lean:270-330`
  changes only the two displayed norm orders from `1` to `3`; quantifier order,
  finite `K`, positive `δ`, `Icc` restart window, exact overlap, strict
  presingular intervals and the non-strict endpoint premise are unchanged.
- The manuscript `H¹` fields occur verbatim as named predicates at
  `formalization/NSFormalization/Section3/T11/Assembly.lean:336-367`, and
  `periodicContinuationAPI_of_h1` uses only those two hypotheses at
  `formalization/NSFormalization/Section3/T11/Assembly.lean:387-395`.
- The mean API agrees with `research/T11/Spec.lean:811-894` at
  `formalization/NSFormalization/Section3/T11/Assembly.lean:401-462`; the
  rescaling API agrees with `research/T11/Spec.lean:933-990` at
  `formalization/NSFormalization/Section3/T11/Assembly.lean:470-519`.

The named source theorems also have the claimed statements: uniqueness and the
lifespan inequality are at
`formalization/NSFormalization/Section3/T11/Uniqueness.lean:26-72`, maximal
uniqueness at `formalization/NSFormalization/Section3/T11/Maximal.lean:294-336`,
the unconditional `H³` restart chain at
`formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean:335-341,345-370,391-420,450-520`,
classical regularity and transport at
`formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean:1140-1210`,
the higher-order bound at
`formalization/NSFormalization/Section3/T11/PairingBound.lean:1737`, the mean
identities at `formalization/NSFormalization/Section3/T11/MeanIdentity.lean:137-171`,
and rescaling classes/inverses at
`formalization/NSFormalization/Section3/T11/Rescaling.lean:69-95`.

There is no vacuity through `⊤.toReal = 0`, an empty interval, or an unused
proof-only binder.  `ClassicalSolutionT` itself carries `0 < T`; restart returns
`0 < δ`; finite bounds use `K ≠ ⊤` and `M ≠ ⊤`; overlap and uniqueness use the
paper's `Ico` intervals.  More strongly, the lane supplies a nonzero admissible
datum and a nonzero compactly supported positive-time force, with positive
horizon and nonzero initial velocity, at
`formalization/NSFormalization/Section3/T11/Assembly.lean:525-568`; its exact
probe is `research/T11/probes/assembly_closes.lean:278-288`.

## 2. What is in Lean

All four claimed canonical terms exist with the exact advertised types:
`periodicLocalTheoryAPI` at
`formalization/NSFormalization/Section3/T11/Assembly.lean:184-192`,
`periodicContinuationH3API` at `:374-382`,
`periodicMeanReductionAPI` at `:457-463`, and
`periodicViscosityRescalingAPI` at `:512-519`.  The closing probe checks all 23
manuscript fields, the two extra narrowed versions, and non-vacuity at
`research/T11/probes/assembly_closes.lean:24-288`.

The contract records the narrowing rather than hiding it
(`verification/Contracts/V1/TorusLocalTheory.lean:19-48`), states both the
manuscript and narrowed structures (`:519-668`), preserves both named `H¹`
predicates (`:670-710`), and registers only the narrowed component in
`TorusLocalTheoryAPI` (`:837-854`).  Every ordinary restated definition has a
canonical `rfl` guard in
`verification/Bindings/TorusLocalTheory.lean:50-190`.  The structure exception
is implemented by fieldwise `toContract`/`ofContract` and `rfl` round trips at
`:198-260`, with the dependent declarations transported at `:262-349`.  The
four APIs are transported at `:355-456`, the two `H¹` predicates and residue
theorem at `:458-496`, and the registered bundle at `:502-528`.

The public test declaration and axiom check are at
`verification/Tests/TorusLocalTheory.lean:25-33`; conformance examples cover
each API and the exact `H¹` residue at `:35-111`.  Registry entry
`T01.torus_local_theory` has version 1, parent `T01`, the correct declaration,
and an explicit narrowing scope at `verification/contracts.json:423-431`.

The sole note is the worker report's malformed appendix citation described on
the first page of this review.  Its mathematical target is nevertheless clear
and the actual cited paper lines agree with the Lean statement.

## 3. Gaps

The reported mathematical gap is honest and complete: uniform local existence
over an `H¹` datum ball, hence the manuscript `restart` and `restartBeyond`
fields, remains unproved (`research/T11/H1_GAP.md:7-35`).  The proved
construction depends on the `H³ × H²` Picard pair
(`research/T11/H1_GAP.md:37-59`).  The consumer audit correctly explains that
T11 feeds order `3` from the all-order bound and that T20's reconciled route
uses the ball-free lifespan criterion (`research/T11/H1_GAP.md:79-102` and
`research/T20/RECONCILIATION.md:66-78`).

I re-grepped the whole requested Section 4 tree.  There is no proved periodic
`H¹` restart lemma there.  The only semantically relevant hits are the named
unproved `ManuscriptHorizonLowerBoundH1` at
`formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean:368-379` and
the proved fixed-force `H⁷` narrowing `RestartFixedForce` at
`formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:14-18,39-62`.
Thus the lane's “not in the tree” claim is accepted.

Hygiene passes for lane 340's Lean files: no executable `sorry`, `admit`,
`axiom`, or `native_decide`; no heartbeat override; the new V1 contract imports
only `Contracts.V1.TorusData` (`verification/Contracts/V1/TorusLocalTheory.lean:1`).
`git diff --diff-filter=M ... -- '*.lean'` is empty, so no existing Lean module
was modified.  The full stacked-branch `git diff --check` reports one blank EOF
line in `research/T11/axioms_classical_regularity.lean:358`, inherited from the
already merged lane 339 portion of this worktree; it is neither a lane-340 Lean
module modification nor a proof/contract defect.

The substantive negative probe changes the registered restart-ball order from
`H³` to `H⁴`, without dropping an argument
(`research/T11/probes/rev340_negative_h4.lean:12-22`).  Direct reuse of the
assembled proof fails for exactly the changed constant: Lean reports that the
term requires `periodicSobolevENorm 3 a' ≤ K` while the mutated target supplies
`periodicSobolevENorm 4 a' ≤ K`.  This is an expected statement mismatch, not a
parser failure or missing import.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; all `lake` commands
were run from `verification/` with `LEAN_NUM_THREADS=6` for builds.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Assembly
exit=0
[cached dependency linter warnings replayed; no line names Assembly]
Build completed successfully (10587 jobs).

$ lake env lean ../formalization/NSFormalization/Section3/T11/Assembly.lean
exit=0, output bytes=0, output lines=0

$ lake env lean Contracts/V1/TorusLocalTheory.lean
exit=0, no output

$ lake env lean Bindings/TorusLocalTheory.lean
exit=0, no output

$ lake env lean Tests/TorusLocalTheory.lean
Contract BlowupDensity.Tests.checkedTorusLocalTheory: checked; standard logical axioms only
exit=0

$ lake env lean ../research/T11/probes/assembly_closes.lean
exit=0, no output
```

The axiom audit output was exactly:

```text
'NSFormalization.Section3.T11.periodicLocalChoiceU' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicLocalHorizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicLocalHorizon_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicLocalSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicLocalHorizon_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicLocalTheoryAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicContinuationH3API' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicContinuationAPI_of_h1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicMeanReductionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicViscosityRescalingAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicLocalTheoryAPI_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`make check` exited 0.  Its exact terminal checks were:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The full gate wrapper exited 0 with these exact result lines:

```text
== make check
== make test
info: Tests/TorusLocalTheory.lean:33:0: Contract BlowupDensity.Tests.checkedTorusLocalTheory: checked; standard logical axioms only
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

The explicit compatibility gate produced:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
exit=0
  "registered_contracts": 39,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The negative probe failed as required:

```text
../research/T11/probes/rev340_negative_h4.lean:22:2: error: Type mismatch
  periodicContinuationH3API.restart
has type
  ... periodicSobolevENorm 3 a' ≤ K ...
but is expected to have type
  ... periodicSobolevENorm 4 a' ≤ K ...
```

Repository/registry checks:

```text
$ git branch --show-current
erenup/340-T11-U17-assembly-contract

$ git log -1 --oneline
6b083981 [340-T11] register T01.torus_local_theory

$ git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- '*.lean'
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 798403004c39e6ff4e5b6d361956eda7396a75bc
[no modified Lean paths]

$ git diff --stat origin/erenup/integration-section3...HEAD -- verification/contracts.json
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 798403004c39e6ff4e5b6d361956eda7396a75bc
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

Verdict: **ACCEPT-WITH-NOTES**.  Fix only the one malformed appendix citation
in `research/T11/REPORT_340.md:7`; no Lean or contract change is required.
