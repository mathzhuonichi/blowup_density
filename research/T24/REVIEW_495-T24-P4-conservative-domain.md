REJECT

Required gate failure: `scripts/gates.sh NSFormalization.Section3.T24.ConservativeOmega`
exits 2 because `experiments/check_contracts.py` rejects the required
`--base-ref origin/erenup/core` option. The same standalone command reproduces
the error. Restore the base-compatibility option/check in `check_contracts.py`
and rerun both commands to `== gates OK` before acceptance.

## 1. What the lane claims

The worker claims the bounded no-slip branch of Proposition 3.17 is closed:
for a smooth spacetime potential, `f = -∇φ`; its pairing with every
divergence-free no-slip classical solution vanishes; and at positive viscosity
every classical solution from rest is zero on `[0,T)`. It also claims a genuine
zero-velocity rest solution with normalized pressure `-φ`, a V2 contract paired
with the retained torus V1 contract, and closure of blueprint node `C317_B`
([`research/T24/REPORT_495.md:5`](REPORT_495.md#L5),
[`research/T24/REPORT_495.md:11`](REPORT_495.md#L11),
[`research/T24/REPORT_495.md:16`](REPORT_495.md#L16),
[`research/T24/REPORT_495.md:31`](REPORT_495.md#L31)).

The article says exactly that the torus force is a periodic negative gradient,
the bounded-domain force is a negative gradient with homogeneous no-slip, and
any smooth zero-initial-velocity solution is zero on its classical lifespan
(`paper/revised/sections/03-torus.tex:537-540`). Its proof first establishes
the pairing by incompressibility plus periodicity/zero normal trace
(`paper/revised/sections/03-torus.tex:541-546`) and then uses the classical
energy identity from zero (`paper/revised/sections/03-torus.tex:547-552`). The
bounded-domain vocabulary is the article's bounded box-or-smooth-domain class
(`paper/revised/sections/03-torus.tex:446-459`). Thus `ContDiff ℝ ∞ φ` is
the Lean spelling of the requested smooth potential, not an analytic condition
beyond "smooth"; no periodicity or compact temporal-support assumption is added.

## 2. What is in Lean

Statement fidelity and proof route pass.

- `conservativeForceOmega` is literally
  `fun z ↦ -pressureGradient φ z.1 z.2`
  (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:25-27`).
- `restSolutionOmega` has zero velocity and pressure
  `domainNormalizePressure Ω (-φ)`
  (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:30-36`).
  Its momentum field rewrites by `residual_domainNormalizePressure` and checks
  the sign directly (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:46-51`);
  its gauge uses boundedness, openness and nonemptiness rather than a vacuous
  `⊤.toReal = 0` convention
  (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:53-58`).
  Pressure-gradient invariance under normalization is proved independently at
  `formalization/NSFormalization/Section3/T23/PressureNormalization.lean:41-54`.
- `potential_pairingOmega` calls `ibp_boundedDomain` and
  `IBP.integral_pressure_energy_zero` directly, using `S.no_slip` and
  `S.divergence`; it does not first prove the velocity is zero
  (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:61-73`).
  The domain IBP supplier is unconditional on the registered domain class
  (`formalization/NSFormalization/Section3/T23/BoundaryIntegration.lean:81-83`),
  and the cited pressure-pairing lemma has exactly the divergence and boundary
  hypotheses claimed
  (`formalization/NSFormalization/Section3/T23/NoSlipEnergy.lean:159-169`).
- `zero_from_restOmega` assumes exactly positive viscosity/horizon, the
  registered nonempty domain, smooth `φ`, and a classical solution from rest
  (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:76-82`).
  It compares with the explicit rest solution, specializes
  `difference_energy_identity`, obtains zero initial energy and a nonpositive
  derivative, applies zero Gronwall, and converts zero integral energy to
  pointwise equality
  (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:83-108`).
  The energy identity cited by the report is the actual no-slip/divergence/IBP
  identity at `formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:193-204`.
- The exported two-field record and theorem have the claimed quantifier order,
  `Ico 0 T`, arbitrary viscosity for pairing, and positive viscosity only for
  zero-from-rest
  (`formalization/NSFormalization/Section3/T24/ConservativeOmega.lean:110-128`).
  `0 < T` makes the interval genuine; the solution record independently stores
  the same horizon positivity
  (`formalization/NSFormalization/Section3/T23/DomainSolution.lean:104-140`).
  The pairing theorem's `_hT` is redundant because the solution already stores
  it, but it is explicitly required by the brief and does not weaken or
  vacuously discharge the conclusion.
- The worker's independent route really uses `velocity_eq_of_ibp` against
  `restSolutionOmega`
  (`research/T24/probes/ConservativeOmega495.lean:9-18`). The public wrapper's
  extra `f ∈ forceClassOmega Ω` input is visible at
  `formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean:12-21`, so
  avoiding that wrapper also avoids adding temporal force support.

The V2 contract is faithful. The force definitions and complete API blocks are
byte-identical between the canonical module and contract (`diff` exit 0 for
canonical lines 26-27 versus contract lines 15-16, and canonical lines 111-123
versus contract lines 19-31). The contract uses the registered V1 boundary
types (`verification/Contracts/V2/ConservativeForcing.lean:1-12`), retains the
V1 torus API as the first conjunct
(`verification/Contracts/V2/ConservativeForcing.lean:33-35`), and the binding
uses the existing fieldwise solution conversion without adding hypotheses
(`verification/Bindings/ConservativeForcingV2.lean:11-28`; conversion at
`verification/Bindings/BoundaryInsertion.lean:415-437`). The V1 registry entry
remains at `verification/contracts.json:225-233`; the V2 entry has the requested
shape and scope at `verification/contracts.json:324-332`; its test audits the
combined contract and three canonical proof declarations at
`verification/Tests/ConservativeForcingV2.lean:7-21`.

Blueprint bookkeeping also passes semantically. `C317_B` is Closed, depends on
the Closed nodes `C317` and `BU`, and has no completion edge
(`formalization/blueprint/proof_graph.json:435-448`; `BU` is Closed at
`formalization/blueprint/proof_graph.json:351-360`). The JSON retains the
schema-required empty value `"completion_from": []`; this produces no dashed
completion relation. The result map and guide point to the correct theorem line
(`formalization/blueprint/RESULT_MAP.md:30`,
`paper/formalization_guide.tex:117-119`), all core/binding/test entrypoints are
present (`formalization/blueprint/entrypoints.json:7`,
`formalization/blueprint/entrypoints.json:34`,
`formalization/blueprint/entrypoints.json:60`), and the generated inventory is
22 Closed / 5 Partial (`README.md:35-42`,
`formalization/blueprint/DEPENDENCY_GRAPH.md:221-227`,
`formalization/blueprint/CLOSURE_AUDIT.md:25-30`).

Non-vacuity and negative checks pass. The reviewer probe constructs the actual
unit box as a nonempty registered domain
(`research/T24/probes/rev495_nonvacuity.lean:12-24`), proves the linear
potential `φ(t,x)=x₀` smooth and nonzero
(`research/T24/probes/rev495_nonvacuity.lean:26-35`), inhabits
`ClassicalSolutionOmega` both for `φ=0` and for that nonzero `φ`
(`research/T24/probes/rev495_nonvacuity.lean:37-53`), and applies the pairing
theorem at the nonzero potential
(`research/T24/probes/rev495_nonvacuity.lean:55-61`). The substantive mutation
copies the solution record but deletes only no-slip
(`research/T24/probes/rev495_drop_no_slip.lean:12-27`); the direct proof then
fails exactly when it needs `S.no_slip`
(`research/T24/probes/rev495_drop_no_slip.lean:31-44`).

## 3. Gaps and findings

1. **Blocking, verification gate.** `scripts/gates.sh:13` always passes
   `--base-ref`, but the current checker only declares `--summary`
   (`experiments/check_contracts.py:115-122`). Consequently both the standard
   lane gate and the separately mandated base-ref command exit 2. This also
   makes the report's statement that no verification gaps remain
   (`research/T24/REPORT_495.md:42-46`) too strong. Restore the prior
   base-compatibility behavior (checking stable contract specifications/tests
   and existing registry entries against the supplied ref), then rerun both
   commands. Merely accepting and ignoring the option would not perform the
   required compatibility check.

No mathematical gap or incorrect theorem statement was found. The report makes
no "not in the tree" or "not in Mathlib" claim; it explicitly declares no
residual (`research/T24/REPORT_495.md:42-53`), so the requested Section4 missing-
lemma grep has no claimed gap to test. The cited reusable lemmas were instead
opened at the exact T23 locations above.

Hygiene passes: the lane adds six Lean files and modifies no pre-existing Lean
module; no added Lean/probe file contains `sorry`, `admit`, an `axiom`
declaration, `native_decide`, or `set_option maxHeartbeats`. The only PDF
changes are the permitted regenerated outputs. Citations and source anchors
resolve under `make paper`.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.

### Canonical module and axioms

`lake build NSFormalization.Section3.T24.ConservativeOmega` exited 0. It emitted
only replayed pre-existing dependency warnings; there was no warning from
`ConservativeOmega.lean`. Exact first and last excerpts (middle omitted under
the raw-output limit):

```text
⚠ [8777/9431] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

...

⚠ [10085/10091] Replayed NSFormalization.Source.BoundedViscosityUniqueness
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
  one_smul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10091 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T24/ConservativeOmega.lean`
exited 0 with exactly 0 output bytes.

`lake env lean ../research/T24/axioms_495.lean` exited 0 with exact output:

```text
'NSFormalization.Section3.T24.conservativeForceOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.restSolutionOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.potential_pairingOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.zero_from_restOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.conservativeForcingOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The worker probe exited 0:

```text
'zero_from_restOmega_uniqueness_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Required gates

`make check` exited 0 with exact output:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2242 source modules; local imports and package paths resolve.
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

`BASE_REF=origin/erenup/core scripts/gates.sh
NSFormalization.Section3.T24.ConservativeOmega` reached `make check`, the module
build, all contract tests, and mutation tests, then exited 2. Exact head/tail:

```text
== make check
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2242 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 30,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.004s

OK
== lake build NSFormalization.Section3.T24.ConservativeOmega
⚠ [8777/8875] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

...

info: Tests/BoundedDomainNorm.lean:33:0: Contract BlowupDensity.Tests.checkedBoundedDomainNormStatement: checked; standard logical axioms only
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
gate_rc=2
```

The separately required command reproduces the same failure exactly:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/core
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
contract_rc=2
```

`make test` exited 0. Exact first/last excerpts:

```text
lake -d verification test
⚠ [8778/8865] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

...

ℹ [10999/11004] Replayed Tests.BoundedDomainNorm
info: Tests/BoundedDomainNorm.lean:28:0: Contract BlowupDensity.Tests.checkedBoundedDomainNorm: checked; standard logical axioms only
info: Tests/BoundedDomainNorm.lean:33:0: Contract BlowupDensity.Tests.checkedBoundedDomainNormStatement: checked; standard logical axioms only
ℹ [11002/11004] Replayed Tests.PeriodicInsertion
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
ℹ [11003/11004] Replayed Tests.TorusNonDensity
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
ℹ [11004/11004] Replayed Tests.TorusMain
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`make test-mutations` exited 0. Exact tail (dependency warnings omitted):

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

### Blueprint, article audit, and paper

`python3 experiments/check_formalization_plan.py` exited 0:

```text
Blueprint: 41 proof nodes, 27 article/guide mappings; 2242 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
```

`python3 experiments/audit_article_axioms.py --build --output-dir
tmp/rev495-article-audit --workers 2` exited 0:

```text
Bindings.CompletedDensity: 8 declarations checked
NSFormalization.Section3.T21.MainAssembly: 33 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.TorusLocalTheory: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
NSFormalization.Section3.T24.ConservativeOmega: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
57 declarations; 27 article entries; 0 forbidden-axiom results
```

`cmp -s tmp/rev495-article-audit/report.json
formalization/blueprint/AXIOM_AUDIT.json` exited 0. Both reports have source hash
`883bd451c00653cd8b6792be4e35391838fd455fcc96b99871077994cbbc5d16`,
57 targets, 27 article rows, zero source tokens, and zero unexpected-axiom
targets.

`make paper` exited 0 with exact output:

```text
make -C paper readers
make[1]: Entering directory '/data_8T/ping/blowup_density/.claude/worktrees/495-T24-P4-conservative-domain/paper'
mkdir -p ../output/pdf
cd revised && latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=../../output/pdf blowup_density_revised.tex
Rc files read:
  /etc/LatexMk
Latexmk: This is Latexmk, John Collins, 31 Jan. 2024. Version 4.83.
Latexmk: Nothing to do for 'blowup_density_revised.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/495-T24-P4-conservative-domain/output/pdf/blowup_density_revised.pdf) are up-to-date

latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=../output/pdf formalization_guide.tex
Rc files read:
  /etc/LatexMk
Latexmk: This is Latexmk, John Collins, 31 Jan. 2024. Version 4.83.
Latexmk: Nothing to do for 'formalization_guide.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/495-T24-P4-conservative-domain/output/pdf/formalization_guide.pdf) are up-to-date

python3 ../experiments/check_reader_documents.py
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 30 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/495-T24-P4-conservative-domain/paper'
```

### Reviewer probes and hygiene

`lake env lean ../research/T24/probes/rev495_nonvacuity.lean` exited 0 with
exactly 0 output bytes. The negative probe exited 1 with the expected exact
error:

```text
../research/T24/probes/rev495_drop_no_slip.lean:42:7: error(lean.invalidField): Invalid field `no_slip`: The environment does not contain `PairingSolutionWithoutNoSlip.no_slip`, so it is not possible to project the field `no_slip` from an expression
  S
of type
  PairingSolutionWithoutNoSlip nu Omega 0 (conservativeForceOmega phi) T
probe_rc=1
```

`git diff --name-only origin/erenup/core...HEAD` exited 0:

```text
README.md
experiments/check_reader_documents.py
formalization/NSFormalization/Section3/T24/ConservativeOmega.lean
formalization/blueprint/AXIOM_AUDIT.json
formalization/blueprint/CLOSURE_AUDIT.md
formalization/blueprint/DEPENDENCY_GRAPH.md
formalization/blueprint/README.md
formalization/blueprint/RESULT_MAP.md
formalization/blueprint/entrypoints.json
formalization/blueprint/proof_graph.json
output/pdf/blowup_density_revised.pdf
output/pdf/formalization_guide.pdf
paper/formalization_guide.tex
research/T24/ATTEMPTS_495.md
research/T24/REPORT_495.md
research/T24/T24_SPLIT.md
research/T24/axioms_495.lean
research/T24/probes/ConservativeOmega495.lean
verification/Bindings/ConservativeForcingV2.lean
verification/Contracts/V2/ConservativeForcing.lean
verification/README.md
verification/Tests/ConservativeForcingV2.lean
verification/contracts.json
```

`git diff --diff-filter=M --name-only origin/erenup/core...HEAD -- '*.lean'`
exited 0 with 0 output bytes: no existing Lean module was modified. The
forbidden-token/max-heartbeat `rg` over all lane/reviewer Lean files exited 1
with 0 output bytes (no matches). `git diff --check origin/erenup/core...HEAD`
exited 0 with 0 output bytes.

Required fix: restore meaningful `--base-ref` compatibility checking in
`experiments/check_contracts.py`, then rerun the standalone base-ref command and
`scripts/gates.sh NSFormalization.Section3.T24.ConservativeOmega` to exit 0 and
print `== gates OK`.

## Lead ruling (2026-09-21 04:40Z)
REJECT reason is the same tooling artefact as lanes 492/493/494 (`check_contracts.py --base-ref` removed by the owner; gates/review scripts fixed). Reviewer confirms statement, proof route (direct IBP pairing), contracts, axioms, non-vacuity, mutation, blueprint, tests, audit and paper checks pass. Merged on lead authority.
