ACCEPT

## 1. What the lane claims

The worker claims three lane-local deliverables: the unconditional periodic
H¹-uniform endpoint theorem `restartBeyondH1T`, a versioned two-field torus H¹
contract with binding/test/registry entry, and closure of blueprint node
`L21_H1` after both the whole-space and torus registrations exist
(`research/P21/REPORT_511.md:8-41`, `research/P21/REPORT_511.md:51-86`).

The mathematical scope is stated honestly.  Current Proposition 2.1 asserts
maximal smooth existence/uniqueness and extension under finite squared-H²
integral (`paper/revised/sections/02-preliminaries.tex:147-157`); its proof uses a
uniform restart time near the endpoint and uniqueness to glue past `S`
(`paper/revised/sections/02-preliminaries.tex:172-182`).  The earlier appendix
source named by the Lean comments says explicitly that H¹ local-existence bounds
give a common duration, that the fixed force is bounded in H¹ on `[0,S+1]`, and
that the periodic mean causes no obstruction (historical
`paper/sections/appendix-a-local-theory.tex:146-155`, opened with
`git show 1a1b53b6^:...`).  The repository assessment correctly records that the
current proposition does not display a separate H¹-uniform clause
(`research/P21/ASSESSMENT.md:18-24`), and the guide describes the new result as a
stronger fixed-force theorem which does not change the article's continuation
proof (`paper/formalization_guide.tex:171-199`).  Thus the lane proves the
brief's isolated stronger obligation without misquoting the current article.

The two new contract fields have exact fidelity.  After replacing only
`periodicSobolevENorm 3` by `periodicSobolevENorm 1`, `diff` of the V1 `restart`
body (`verification/Contracts/V1/TorusLocalTheory.lean:473-481`) against V2
(`verification/Contracts/V2/TorusLocalTheory.lean:26-34`) is empty; the same is
true for V1 `restartBeyond`
(`verification/Contracts/V1/TorusLocalTheory.lean:502-515`) against V2
(`verification/Contracts/V2/TorusLocalTheory.lean:38-51`).  In particular, `δ`
precedes `t₀` and the datum, the restart time uses `Icc 0 S`, trajectory and
overlap use `Ico 0 S`, and both velocity and normalized pressure are preserved.
The pressure is genuinely normalized by the `PressureGaugeT` field of every
`ClassicalSolutionT` (`verification/Contracts/V1/TorusLocalTheory.lean:54-67`,
`verification/Contracts/V1/TorusLocalTheory.lean:83-134`).

There is no vacuity or silent extra analytic input.  The statements require
`0 < δ`, positive viscosity, a finite radius `K ≠ ⊤`, and the advertised
nonempty time conditions (`verification/Contracts/V2/TorusLocalTheory.lean:26-51`).
`h1RestartT` has no named supplier argument and constructs its duration from the
proved uniform H¹ lifespan theorem
(`formalization/NSFormalization/Section3/T11/H1Restart.lean:542-590`).  The
endpoint theorem likewise has no named supplier; it applies `h1RestartT` at `S`
and keeps its duration `d`
(`formalization/NSFormalization/Section3/T11/H1RestartBeyond.lean:28-48`).

## 2. What is in Lean

Every declaration claimed by the report exists with the claimed type:

- `restartBeyondH1T` is exactly the expanded `h1UniformEndpointT` target
  (`formalization/NSFormalization/Section3/T11/H1RestartBeyond.lean:28-42`,
  `research/P21/Targets.lean:63-76`).  The literal conformance example compiles
  (`research/P21/probes/b5t_endpoint.lean:20-35`).
- Its proof is the established `restartBeyond` skeleton with the sole supplier
  call changed from `restart H` to `h1RestartT`: compare
  `formalization/NSFormalization/Section3/T11/RestartBeyond.lean:408-450` with
  `formalization/NSFormalization/Section3/T11/H1RestartBeyond.lean:28-73`.
  The proof chooses `t₀ = max 0 (S-d/2)`, returns `δ=t₀+d-S`, and invokes
  both velocity and pressure uniqueness on every strict old time
  (`formalization/NSFormalization/Section3/T11/H1RestartBeyond.lean:44-73`).
- `PeriodicContinuationH1API` contains exactly the two required fields, and
  `torusLocalTheoryV2Statement` is exactly
  `Nonempty TorusLocalTheoryAPI ∧ PeriodicContinuationH1API`
  (`verification/Contracts/V2/TorusLocalTheory.lean:23-56`).  It imports V1 and
  restates no vocabulary, so no new definitional bridge is missing
  (`verification/Contracts/V2/TorusLocalTheory.lean:1-20`).
- The binding supplies the two fields from `h1RestartT` and
  `restartBeyondH1T`, using `toContract`, the regularity equivalence, and the
  `SolvesBelowT` equivalence (`verification/Bindings/TorusLocalTheoryV2.lean:27-49`).
  The reused solution conversion is fieldwise and its velocity/pressure and
  round-trip bridges are `rfl`
  (`verification/Bindings/TorusLocalTheory.lean:192-260`); the regularity and
  `SolvesBelowT` transports are explicit
  (`verification/Bindings/TorusLocalTheory.lean:299-307`,
  `verification/Bindings/TorusLocalTheory.lean:331-349`).
- `checkedTorusLocalTheoryV2` and exact projections of both fields are in the
  warning-as-error test module
  (`verification/Tests/TorusLocalTheoryV2.lean:17-51`,
  `verification/lakefile.toml:25`).
- Registry entry `T01.torus_local_theory_v2` has parent `T11`, version 2, the
  correct modules/declaration/scope, is enabled, and leaves V1 registered
  (`verification/contracts.json:158-178`).  The registry contains 36 entries.

The closure bookkeeping is internally consistent.  `L21_H1` is `Closed`, has
`completion_from: []`, depends only on Closed nodes `L21T` and `L21R`, and all
six evidence paths exist (`formalization/blueprint/proof_graph.json:65-95`).  It
remains in the shared-construction panel
(`formalization/blueprint/proof_graph.json:621-629`).  The Proposition 2.1 row is
Closed with all nine source anchors
(`formalization/blueprint/RESULT_MAP.md:9-12`); every anchor was checked against
the named declaration.  The guide has the same sources and a mathematically
accurate enstrophy-barrier explanation
(`paper/formalization_guide.tex:81-92`,
`paper/formalization_guide.tex:171-204`).  README reports 27 Closed and 0
Partial (`README.md:28-42`), the reader check has `partial = set()`
(`experiments/check_reader_documents.py:55-71`), the generated graph shows the
two Closed dependencies (`formalization/blueprint/DEPENDENCY_GRAPH.md:21-39`),
and the closure audit explains that no quantitative local-existence input
remains (`formalization/blueprint/CLOSURE_AUDIT.md:16-32`).  Both rebuilt PDFs
exist; text extraction shows “Proposition 2.1 Closed” with the new sources.

The recorded axiom audit is fresh and exact.  It records source hash
`488abf2e...`, 2292 files, and only the three allowed logical axioms
(`formalization/blueprint/AXIOM_AUDIT.json:1-10`); its torus binding entry has no
unexpected axioms (`formalization/blueprint/AXIOM_AUDIT.json:103-114`) and its
Proposition 2.1 row is Closed
(`formalization/blueprint/AXIOM_AUDIT.json:1005-1020`).  The freshly generated
`tmp/article-audit/report.json` is byte-identical to the tracked audit.

Hygiene is clean.  The lane-local proof/contract/binding/test/probes contain no
`sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats`.  The required
`git diff --name-only origin/erenup/core...HEAD` reports multiple merge bases and
includes the explicitly inherited 503/506/507/508/510 files.  Using the lane's
actual post-inheritance base `1cc77024`, the only Lean changes are four new
files—`H1RestartBeyond.lean`, the V2 contract, binding, and test—plus the registry;
no earlier lane module or V1 file was modified by lane 511.  The only existing
proof-module modification visible in the combined branch is commit `73d1af5b`
to `Section4/A04/EnstrophyInequality.lean`, inherited from lane 510; it is exactly
the four deferred one-line linter cleanups authorized at
`research/P21/REVIEW_504-P21-B1-enstrophy-r3.md:1-8`.

## 3. Gaps and negative checks

No mathematical or registration gap remains for this lane.  The worker report
does not claim that any lemma is absent from the Section 4 tree; its “gaps”
section explicitly says there is no remaining P6/L21_H1 gap
(`research/P21/REPORT_511.md:95-103`).  Therefore the requested whole-tree
missing-lemma grep has no gap claim to validate.  A search of that report for
`not in the tree|missing lemma|remaining gap` found only the affirmative “no
remaining ... gap” sentence.

The substantive reviewer mutation is
`research/P21/probes/rev511_widen_overlap.lean:21-36`: it widens both required
overlap intervals from `[0,S)` (`Ico`) to `[0,S]` (`Icc`), without deleting an
argument.  Direct Lean rejects it for exactly the expected endpoint mismatch:

```text
../research/P21/probes/rev511_widen_overlap.lean:36:2: error: Type mismatch
  restartBeyondH1T
has type
  ...
    ∃ v,
      (∀ t ∈ Ico 0 S, ∀ (x : Space), v.velocity (t, x) = u (t, x)) ∧
        ∀ t ∈ Ico 0 S, ∀ (x : Space), v.pressure (t, x) = p (t, x)
but is expected to have type
  ...
    ∃ v,
      (∀ t ∈ Icc 0 S, ∀ (x : Space), v.velocity (t, x) = u (t, x)) ∧
        ∀ t ∈ Icc 0 S, ∀ (x : Space), v.pressure (t, x) = p (t, x)
```

Non-vacuity is independently witnessed by the existing registered probe.  It
constructs a genuine zero periodic classical solution on every positive
horizon (`research/P21/probes/b5t_registered.lean:27-87`), chooses the finite
actual radius `periodicSobolevENorm 1 0`, and instantiates registered
`restartBeyond` to obtain a positive `δ` and a solution on `1+δ` with literal
velocity and normalized-pressure overlap
(`research/P21/probes/b5t_registered.lean:89-114`).  That file compiles.

## 4. Commands and results

All Lean/Lake commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.

1. `lake build NSFormalization.Section3.T11.H1RestartBeyond` — exit 0.  Lake
   replayed inherited dependency warnings but emitted no diagnostic for the new
   module.  First and last relevant output (middle omitted):

```text
⚠ [8778/9334] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply
[... inherited replay output omitted ...]
⚠ [10674/10675] Replayed NSFormalization.Section3.T11.H1Restart
warning: NSFormalization/Section3/T11/H1Restart.lean:244:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Build completed successfully (10675 jobs).
```

2. `lake env lean ../formalization/NSFormalization/Section3/T11/H1RestartBeyond.lean`
   — exit 0, exact output:

```text
[no output]
```

   `lake env lean ../research/P21/probes/b5t_endpoint.lean` also exited 0 with
   no output.  `lake env lean Tests/TorusLocalTheoryV2.lean` exited 0:

```text
Contract BlowupDensity.Tests.checkedTorusLocalTheoryV2: checked; standard logical axioms only
```

3. `lake env lean ../research/P21/axioms_b5t.lean` — exit 0, exact output:

```text
'NSFormalization.Section3.T11.restartBeyondH1T' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.restartBeyondH1T: checked; standard logical axioms only
'BlowupDensity.Bindings.torusContinuationH1API' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Bindings.torusContinuationH1API: checked; standard logical axioms only
'BlowupDensity.Bindings.torusLocalTheoryV2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Bindings.torusLocalTheoryV2_holds: checked; standard logical axioms only
'BlowupDensity.Tests.checkedTorusLocalTheoryV2' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Tests.checkedTorusLocalTheoryV2: checked; standard logical axioms only
```

4. `lake env lean ../research/P21/probes/b5t_registered.lean` — exit 0, exact
   output; the zero-solution example follows these commands in the same checked
   file:

```text
'BlowupDensity.Tests.checkedTorusLocalTheoryV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedContinuationV3' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Tests.checkedTorusLocalTheoryV2: checked; standard logical axioms only
Contract BlowupDensity.Tests.checkedContinuationV3: checked; standard logical axioms only
```

5. Independent owner checks all exited 0:

```text
$ python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2281 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.

$ python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 36,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}

$ python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.004s

OK
```

6. `python3 experiments/audit_article_axioms.py --build --output-dir
   tmp/article-audit --workers 2` — exit 0, exact output:

```text
NSFormalization.Section3.T17.ArticleScope: 9 declarations checked
NSFormalization.Section3.T21.MainAssembly: 30 declarations checked
Bindings.CompletedDensity: 8 declarations checked
Bindings.ForceAmplitude: 6 declarations checked
Bindings.MultipleRegionsV2: 5 declarations checked
Bindings.ContinuationV3: 3 declarations checked
Bindings.TorusLocalTheoryV2: 2 declarations checked
Bindings.PeriodicInsertionV2: 2 declarations checked
Bindings.BoundaryInsertionV2: 2 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeOmega: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
76 declarations; 27 article entries; 0 forbidden-axiom results
```

   `sha256sum` gave the same digest for the tracked and fresh reports:

```text
5f3c6e266431c788a7707ee1b43c954c20a8797720bbaacc5f2dfb59c837e3d9  formalization/blueprint/AXIOM_AUDIT.json
5f3c6e266431c788a7707ee1b43c954c20a8797720bbaacc5f2dfb59c837e3d9  tmp/article-audit/report.json
```

7. `make check` was rerun after the audit — exit 0, exact output:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2281 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 36,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

8. `make test` — exit 0.  First and last relevant output (middle omitted):

```text
lake -d verification test
⚠ [8778/9205] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[... inherited replay output omitted ...]
ℹ [11014/11043] Replayed Tests.TorusLocalTheoryV2
info: Tests/TorusLocalTheoryV2.lean:21:0: Contract BlowupDensity.Tests.checkedTorusLocalTheoryV2: checked; standard logical axioms only
ℹ [11041/11043] Replayed Tests.PeriodicInsertion
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
ℹ [11042/11043] Replayed Tests.TorusNonDensity
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
ℹ [11043/11043] Replayed Tests.TorusMain
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

9. `make test-mutations` — exit 0.  First and last relevant output (middle
   omitted):

```text
python3 experiments/test_contract_mutations.py
⚠ [8778/9448] Replayed NSFormalization.Source.FiniteHilbertBochner
[... inherited build/test replay output omitted ...]
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

10. `make paper` — exit 0, exact substantive output:

```text
make -C paper readers
make[1]: Entering directory '/data_8T/ping/blowup_density/.claude/worktrees/511-P21-B5-torus-closure/paper'
mkdir -p ../output/pdf
cd revised && latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=../../output/pdf blowup_density_revised.tex
Latexmk: Nothing to do for 'blowup_density_revised.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/511-P21-B5-torus-closure/output/pdf/blowup_density_revised.pdf) are up-to-date
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=../output/pdf formalization_guide.tex
Latexmk: Nothing to do for 'formalization_guide.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/511-P21-B5-torus-closure/output/pdf/formalization_guide.pdf) are up-to-date
python3 ../experiments/check_reader_documents.py
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 36 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/511-P21-B5-torus-closure/paper'
```

   The independent `python3 experiments/check_reader_documents.py` run printed
   the same seven reader-check lines and exited 0.

11. `scripts/gates.sh NSFormalization.Section3.T11.H1RestartBeyond
    Contracts.V2.TorusLocalTheory Bindings.TorusLocalTheoryV2
    Tests.TorusLocalTheoryV2` — exit 0.  First and last output (middle omitted):

```text
== make check
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2281 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
[... build and test output omitted ...]
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
{
  "registered_contracts": 36,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

12. `git diff --check` — exit 0, exact output:

```text
[no output]
```

No fixes are required.
