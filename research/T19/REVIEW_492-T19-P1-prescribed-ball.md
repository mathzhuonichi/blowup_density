REJECT — the required contract-diff gate is not runnable: `check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core` (exit 2), and `scripts/gates.sh` fails at the same command.

## 1. What the lane claims

The worker claims a complete article-level close of Theorem 3.6 for every
prescribed positive-radius coordinate ball whose closure lies in the interior
of the fundamental cube.  Specifically, it claims:

- a genuine prescribed-centre/radius `placementDataAt`, with definitional
  projections;
- an assembled prescribed-ball insertion family and all T18 exports, stated
  against the original `reference.velocity`;
- an article-scope `periodicInsertion_from_data` whose only inputs are positive
  viscosity, the prescribed ball, admissible datum/force, positive `T, δ`, and
  a classical reference through `T + δ`;
- all four clauses of `thm:insertion`, including single-chart `O(ε)` support;
- a token-for-token V2 contract/binding/test, while retaining V1;
- a non-vacuous centred and off-centre zero-reference instance; and
- closure of `G36_FULL`, the 22 Closed / 5 Partial counts, regenerated audit and
  reader artifacts.

Those mathematical and bookkeeping claims are accurate.  The rejection is
solely the mandatory gate failure documented in Part 4.

## 2. What is in Lean

### Statement fidelity

The paper says: smooth reference on `[0,T+δ]`, arbitrary nonempty coordinate
ball, exact lifespan/blowup, unchanged history, divergence-free shrinking
support inside the chosen ball, the three simultaneous bounds, and the
negative-order limit (`paper/revised/sections/03-torus.tex:197-221`).

`periodicInsertion_from_data` has precisely the requested input telescope:
`ν>0`, arbitrary `center`, `radius>0`,
`closure (ball center radius) ⊆ interior fundamentalCube`, `a∈initialClassT`,
`g∈forceClassT`, `T>0`, `δ>0`, and
`reference : ClassicalSolutionT ν a g (T+δ)`
(`formalization/NSFormalization/Section3/T19/FromData.lean:20-25`).  Its
threshold, force/velocity families, and constants are all chosen before `ε`
and all norm indices (`FromData.lean:26-34`).  Thus no constant is allowed to
depend on the scale or on `p,q,s`.

The conclusion contains:

- force and force-difference membership, exact
  `maximalLifespanT = ENNReal.ofReal T`, a pinned classical solution, and the
  limsup blowup (`FromData.lean:35-39`);
- equality with `reference.velocity` through `T-2ε²`
  (`FromData.lean:40-41`);
- divergence-free difference and
  `tsupport(...) ∩ fundamentalCube ⊆ ball center (ε*R)`, with that ball inside
  the prescribed ball (`FromData.lean:42-47`);
- Eclose, Fclose, and Hsclose with the registered membership/path guards
  (`FromData.lean:48-57`); and
- negative-order membership and convergence (`FromData.lean:31-33,58`).

The support radius is honest: `R>0` is explicit (`FromData.lean:28`), and an
admissible `ε` is positive, so the displayed ball is not empty through a
nonpositive-radius trick.  The real-valued right sides do not use
`⊤.toReal = 0`.  `M,D,C` are nonnegative, the mixed constants are nonnegative,
and the Sobolev constants are positive on their stated range
(`FromData.lean:28-30`).  Every named hypothesis is used in the construction or
transport (`FromData.lean:59-84`); there are no unused article binders or extra
caller-supplied analytic records.

`placementDataAt` stores exactly the requested `center`, `radius`, and `x₀`,
and stores `hcube` as `chartBall_in_cube`
(`formalization/NSFormalization/Section3/T15/PlacementAt.lean:11-29`).  Its
four requested projection lemmas are all `rfl` (`PlacementAt.lean:53-63`).
This is the one-region factorisation of the existing T24 construction, whose
corresponding fields and radius-adapted threshold occur at
`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:47-83`.
Neither T24 nor the fixed `placementData` module was edited.

The prescribed construction selects the registered packet, uses
`placementDataAt`, and builds the correction at
`min (radius/2) (1/4)` (`formalization/NSFormalization/Section3/T19/ThreadingAt.lean:24-62`).
The T18 assembly and raw premises are supplied at `ThreadingAt.lean:64-73`.
The zero extension is identified with the original reference slice at
`ThreadingAt.lean:191-204`; divergence, single-chart support, and energy are
then transported at `ThreadingAt.lean:206-251`.  The single-chart reduction
uses the proved lattice separation lemma (`ThreadingAt.lean:170-189`) and the
canonical T18 periodic-support and chart-containment fields
(`formalization/NSFormalization/Section3/T18/Assembly.lean:110-130`).  This is
the correct torus formulation: the whole periodic lift is not falsely placed
inside one Euclidean ball.

The V2 contract body is token-identical to `FromData.lean:21-58` after the
required registered-vocabulary spelling
`BlowupDensity.Contracts.V1.alpha` for implementation `alphaT`
(`verification/Contracts/V2/PeriodicInsertion.lean:16-54`).  The binding only
converts the separately defined classical-solution structure and rewrites the
lifespan definition (`verification/Bindings/PeriodicInsertionV2.lean:10-25`);
the fieldwise conversions and lifespan bridge are at
`verification/Bindings/TorusLocalTheory.lean:192-274`.  The test checks the V2
declaration, raw theorem, and support theorem (`verification/Tests/PeriodicInsertionV2.lean:7-13`).
V1 remains registered beside V2 (`verification/contracts.json:247,324-332`).

The off-centre non-vacuity witness uses centre `(1/4,1/4,1/4)`, radius `1/8`,
an explicit cube-containment proof, zero datum/force, and the constant zero
reference (`research/T19/probes/prescribed_ball_492.lean:28-63`).  It compiles
with no output.  Hence neither the ball hypotheses nor the raw reference
hypotheses are vacuous.

### Blueprint, citations, and hygiene

`G36_FULL` is Closed, has evidence in the prescribed-ball modules/binding, has
`depends_on: ["G36"]`, and has no nonempty completion link
(`formalization/blueprint/proof_graph.json:209-222`).  The result map is Closed
(`formalization/blueprint/RESULT_MAP.md:19`), the guide row is Closed and names
all four clauses (`paper/formalization_guide.tex:98-101`), and the inventory is
22 Closed / 5 Partial (`README.md:35`,
`formalization/blueprint/DEPENDENCY_GRAPH.md:223`).  The registry entry has the
requested ID and scope (`verification/contracts.json:324-332`).  Its fresh
56-declaration audit was byte-identical to the tracked
`formalization/blueprint/AXIOM_AUDIT.json`.

`git diff --name-status origin/erenup/core...HEAD -- '*.lean'` lists only new
Lean files; no pre-existing Lean module was modified.  A scan of all changed
Lean plus the reviewer probe found no `sorry`, `admit`, `axiom`,
`native_decide`, or `maxHeartbeats`.  The implementation has exactly 33 public
declarations (5 in PlacementAt, 27 in ThreadingAt, 1 in FromData), matching the
axioms file.  `git diff --check` is clean.

The worker report declares no missing lemma or “not in the tree” residual
(`research/T19/REPORT_492.md:114-131`), so the mandatory whole-Section4 search
has no missing-lemma target; a grep of the report and ATTEMPTS found no such
claim.

### Negative check

The permitted reviewer probe changes the main exact-lifespan constant from
`T` to `T+δ` (`research/T19/probes/rev492_lifespan_mutation.lean:12-25`).  This
is a substantive mutation of clause (i), not a dropped application argument.
Lean rejects it with exactly the expected mismatch:

```text
../research/T19/probes/rev492_lifespan_mutation.lean:25:2: error: Type mismatch
  (hall ε hε).right.right.left
has type
  maximalLifespanT ν a (force ε) = ENNReal.ofReal T
but is expected to have type
  maximalLifespanT ν a (force ε) = ENNReal.ofReal (T + δ)
```

## 3. Gaps

There is no mathematical, statement-fidelity, axiom, non-vacuity, citation, or
publication-bookkeeping gap found in the lane.

There is one blocking acceptance gap.  `scripts/gates.sh:13` always passes
`--base-ref` to `experiments/check_contracts.py`, but that program's parser
accepts only `--summary` (`experiments/check_contracts.py:115-118`).  Because
verification was touched, the review brief requires both that exact direct
command and `scripts/gates.sh`; both exit 2.  This mismatch is already present
in `origin/erenup/core`, and the lane did not modify either file, but it still
means the required gate suite is not green.  A successful `make check` is not a
substitute: it invokes `check_contracts.py --summary`, not the base-ref check.

Required fix: make `check_contracts.py --base-ref origin/erenup/core` a
supported, meaningful diff-aware check (or align the prescribed gate interface
in the core process layer), then rerun the direct command and
`scripts/gates.sh NSFormalization.Section3.T19.FromData`.  No Lean theorem
change is requested.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`; Lake ran only from
`verification/` with `LEAN_NUM_THREADS=6`.

### Main module build and direct typecheck

`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.FromData`
returned 0.  It emitted only replayed dependency warnings; the exact first and
last excerpts are:

```text
⚠ [8778/9023] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9822/10048] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
[middle replayed dependency warnings omitted]
⚠ [10505/10662] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10556/10662] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10557/10662] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10662 jobs).
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T19/FromData.lean`
returned 0 with exactly no output.

### Axioms and probes

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T19/axioms_492.lean`
returned 0.  All 33 `#print axioms` results have exactly the same set.  First
and last excerpts:

```text
'NSFormalization.Section3.T15.placementDataAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementDataAt_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementDataAt_chartCenter' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementDataAt_chartRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.placementDataAt_x₀' depends on axioms: [propext, Classical.choice, Quot.sound]
[23 declarations with the identical axiom set omitted]
'NSFormalization.Section3.T19.At.diffSupport_in_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.At.velocityDifference_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.At.energyRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.At.exists_force_close_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.periodicInsertion_from_data' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T19/probes/prescribed_ball_492.lean` returned 0
with exactly no output.  The mutation command returned 1 with the exact error
quoted in Part 2.

### Repository gates

`LEAN_NUM_THREADS=6 make check` returned 0:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2244 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 30,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

`LEAN_NUM_THREADS=6 make test` returned 0 and completed 11006 jobs.  The last
relevant lines were:

```text
ℹ [10938/11006] Replayed Tests.PeriodicInsertionV2
info: Tests/PeriodicInsertionV2.lean:11:0: Contract BlowupDensity.Tests.checkedPeriodicInsertionV2: checked; standard logical axioms only
info: Tests/PeriodicInsertionV2.lean:12:0: Contract NSFormalization.Section3.T19.periodicInsertion_from_data: checked; standard logical axioms only
info: Tests/PeriodicInsertionV2.lean:13:0: Contract NSFormalization.Section3.T19.At.velocityDifference_support: checked; standard logical axioms only
[other registered tests omitted]
ℹ [11006/11006] Replayed Tests.TorusMain
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`LEAN_NUM_THREADS=6 make test-mutations` returned 0.  Its exact tail was:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`LEAN_NUM_THREADS=6 make paper` returned 0:

```text
make -C paper readers
make[1]: Entering directory '/data_8T/ping/blowup_density/.claude/worktrees/492-T19-P1-prescribed-ball/paper'
mkdir -p ../output/pdf
cd revised && latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=../../output/pdf blowup_density_revised.tex
Rc files read:
  /etc/LatexMk
Latexmk: This is Latexmk, John Collins, 31 Jan. 2024. Version 4.83.
Latexmk: Nothing to do for 'blowup_density_revised.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/492-T19-P1-prescribed-ball/output/pdf/blowup_density_revised.pdf) are up-to-date

latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=../output/pdf formalization_guide.tex
Rc files read:
  /etc/LatexMk
Latexmk: This is Latexmk, John Collins, 31 Jan. 2024. Version 4.83.
Latexmk: Nothing to do for 'formalization_guide.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/492-T19-P1-prescribed-ball/output/pdf/formalization_guide.pdf) are up-to-date

python3 ../experiments/check_reader_documents.py
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 30 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/492-T19-P1-prescribed-ball/paper'
```

The fresh article audit returned 0, and its generated `report.json` was
byte-identical to the tracked audit:

```text
Bindings.CompletedDensity: 8 declarations checked
NSFormalization.Section3.T21.MainAssembly: 31 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
Bindings.PeriodicInsertionV2: 3 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
56 declarations; 27 article entries; 0 forbidden-axiom results
```

### Blocking required commands

`python3 experiments/check_contracts.py --base-ref origin/erenup/core`
returned 2 with exact output:

```text
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
```

`BASE_REF=origin/erenup/core scripts/gates.sh NSFormalization.Section3.T19.FromData`
also returned 2.  Its initial checks/build/tests passed, but its exact final
output was:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
```

The script never printed `== gates OK`.

## Lead ruling (2026-09-21 04:25Z)
REJECT reason is the same tooling artefact as lane 493: the owner's `check_contracts.py` has no `--base-ref` (gates/review scripts now use `--summary`/`make check`). Reviewer confirms mathematics, fidelity, axioms, mutation, non-vacuity, contracts and bookkeeping pass. Merged on lead authority.
