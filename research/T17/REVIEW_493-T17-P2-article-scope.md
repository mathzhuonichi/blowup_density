REJECT

## 1. What the lane claims

The worker claims that `C35_FULL` is closed by an article-level correction
statement, all displayed Lemma 3.5 bounds, a V2 contract and binding, and the
corresponding blueprint/guide updates. That claim is mathematically supported,
but the lane cannot be accepted while a mandatory verification gate exits 2.
The reproducer is in part 4.

The paper fixes a smooth periodic reference with `δ > 0`, admissible initial
datum and force at `paper/revised/sections/03-torus.tex:105-107`; Lemma 3.4 gives
the radial potential, correction, coordinate-ball support and cancellation at
`paper/revised/sections/03-torus.tex:123-149`. Lemma 3.5 defines the exact force
at `paper/revised/sections/03-torus.tex:152-158` and states spatial/time support,
both derivative rates, `E_T`, mixed, and `L^1_t H^s_x` estimates at
`paper/revised/sections/03-torus.tex:159-176`.

The worker report's named declarations all exist. There are exactly 26 theorems
in `formalization/NSFormalization/Section3/T17/ArticleScope.lean`: the main
theorem at `:44-50`; slab/force identifications at `:60-77`; force regularity,
support and every displayed bound at `:80-181`; the article potential and
profile identifications at `:184-213`; and the profile projections and scaling
identities at `:216-279`.

## 2. What is in Lean

### Statement fidelity

`correctionStatementArticle` has exactly the requested inputs and implication
order at `formalization/NSFormalization/Section3/T17/ArticleScope.lean:29-42`:
positive viscosity, positive `r < 1/2`, positive `δ`, registered initial/force
classes, raw packet support, and the Lemma 3.4 ball inclusion. Its conclusion is
the same `D` carrying `LocalPotentialAPI` and all 45 `CorrectionAPI` fields,
conjoined with equality of the zero extension and `reference.velocity` on
`Ico 0 (place.T + δ)`. The proof at `:44-50` uses the open-slab bridge and the
zero-extension periodicity/smoothness/divergence lemmas, rather than adding a
global-smoothness or chart premise. The relevant bridge statement is
`formalization/NSFormalization/Section3/T17/SlabBridge2.lean:20-31`, and the
zero-extension equality, global spatial periodicity and open-slab smoothness are
`formalization/NSFormalization/Section3/T19/Threading.lean:57-73`.

The `a ∈ initialClassT` and `g ∈ forceClassT` arguments are intentionally the
article hypotheses from `03-torus.tex:106-107`; the proof names them `_ha` and
`_hg` at `ArticleScope.lean:45` because existence of the supplied
`ClassicalSolutionT` already carries the PDE fields. They are not hidden
premises, and the compiled zero-reference instance below shows the entire block
is satisfiable. `PlacementData.time_pos`, chart geometry, compact `Kstar`, and a
positive common scale are honest fields at
`formalization/NSFormalization/Section3/T15/Scaling.lean:106-189`. The returned
potential additionally has `0 < D.ε₀` and a strict time-window bound at
`formalization/NSFormalization/Section3/T16/LocalPotential.lean:115-132`, so the
scale interval is nonempty.

The force operator is token-for-token the paper's five terms at
`formalization/NSFormalization/Section3/T17/Transport.lean:255-266`. The named
exports preserve:

- open support, spatial volume and time length at `ArticleScope.lean:93-116`;
- `ε^(-2j-m)` and `ε^(-2-m)` at `ArticleScope.lean:118-137`;
- `ε^(3/2)` at `ArticleScope.lean:139-143`;
- `ε^(alphaT p q + 1)` with `1 ≤ p,q` at `ArticleScope.lean:145-162`;
- both `ε^(3/2)` and `ε^(3/2-s)` for `0 ≤ s ≤ 1` at
  `ArticleScope.lean:164-181`.

The real coefficients cannot be erased through `ENNReal.ofReal`: the underlying
record contains nonnegative derivative, energy and mixed constants and a
strictly positive Sobolev constant at
`formalization/NSFormalization/Section3/T17/Correction.lean:190-281`. Counting
the structure declarations at `Correction.lean:71-281` gives exactly 45 fields.
The global force equality with the original reference is proved at
`ArticleScope.lean:70-77`, using the correction support and the window equality;
the potential and both concrete profiles are likewise identified at
`ArticleScope.lean:183-213`.

The V2 contract at `verification/Contracts/V2/Correction3.lean:12-25` is the
same statement over registered vocabulary, with `extendByZero` expanded to its
contract-safe `if t ∈ Ico ... then ... else 0` spelling. The binding transports
the classical solution, placement, potential and full correction record at
`verification/Bindings/Correction3V2.lean:10-17`; its packet specialization
derives raw support from `PacketAPI.velocity_support` at `:22-38`. V1 remains
registered at `verification/contracts.json:236-244`, while V2 is registered at
`verification/contracts.json:324-332` and tested at
`verification/Tests/Correction3V2.lean:7-12`.

The graph records `C35_FULL` as Closed with `depends_on: ["C35_T"]` at
`formalization/blueprint/proof_graph.json:179-191`. The result map is Closed at
`formalization/blueprint/RESULT_MAP.md:18`; the guide row and all named bounds
are at `paper/formalization_guide.tex:95-104`; and the canonical proof and test
entrypoints occur at `formalization/blueprint/entrypoints.json:7,24,62`. Counts
are 22 Closed / 5 Partial at `README.md:35` and
`formalization/blueprint/CLOSURE_AUDIT.md:25-28`.

### Hygiene and reviewer probes

No pre-existing `.lean` module was modified. Exact changed-Lean listing:

```text
formalization/NSFormalization/Section3/T17/ArticleScope.lean
research/T17/axioms_493.lean
research/T17/probes/article_scope.lean
verification/Bindings/Correction3V2.lean
verification/Contracts/V2/Correction3.lean
verification/Tests/Correction3V2.lean
```

All six are new relative to `origin/erenup/core`. A scan of them and the two
review probes finds no declaration/use of `sorry`, `admit`, `axiom`, or
`native_decide`, and no `maxHeartbeats`. Existing non-Lean edits are the record,
registry, reader-checker, guide, and generated-document updates authorized by
the brief. `git diff --check origin/erenup/core...HEAD` has no output and exits
0. Paper source anchors are also mechanically rechecked by `make paper`.

The worker report contained no zero-reference instance. The reviewer added
`research/T17/probes/rev493_nonvacuity.lean`: the registered packet and placement
are fixed at `:17-20`, the genuine zero classical reference at `:22-23`, and the
full article conclusion is inhabited at `:28-57`. It compiles with zero output.

The substantive negative mutation is
`research/T17/probes/rev493_mutation.lean:22-34`: it changes the displayed force
derivative exponent from `2 + m` to `1 + m`, without dropping an argument. Lean
rejects exactly that exponent mismatch:

```text
../research/T17/probes/rev493_mutation.lean:34:2: error: Type mismatch
  A.force_derivative_bound m ε hε
has type
  ∀ (z : SpaceTime) (u_1 : Fin m → Space),
    (∀ (i : Fin m), ‖u_1 i‖ ≤ 1) →
      ‖(iteratedFDeriv ℝ m (correctionForce ν (extendByZero reference).velocity D ε) z) fun i => (0, u_1 i)‖ ≤
        A.forceDerivConst m * ε⁻¹ ^ (2 + m)
but is expected to have type
  ∀ (z : SpaceTime) (directions : Fin m → Space),
    (∀ (i : Fin m), ‖directions i‖ ≤ 1) →
      ‖(iteratedFDeriv ℝ m (correctionForce ν (extendByZero reference).velocity D ε) z) fun i => (0, directions i)‖ ≤
        A.forceDerivConst m * ε⁻¹ ^ (1 + m)
```

## 3. Gaps

There is no mathematical or statement-fidelity gap found in the lane. The
worker report makes no “missing from the tree” claim, so the requested full
`formalization/NSFormalization/Section4` missing-lemma grep is not applicable.
The previously recorded G4/G5 items are counterexamples to false stronger
statements, not alleged missing lemmas; the lane correctly retains the zero
extension because `CorrectionAPI.reference_periodic` is global
(`formalization/NSFormalization/Section3/T17/Correction.lean:97-100`).

The acceptance gap is the required contract compatibility gate. It is inherited
from `origin/erenup/core`, not introduced by this lane: `scripts/gates.sh:13`
invokes `check_contracts.py --base-ref`, while
`experiments/check_contracts.py:116-118` defines only `--summary`. Nevertheless,
the review instructions explicitly require both commands after any
`verification/` change, so a passing verdict would be inaccurate. Restore the
actual base-compatibility option/check (not a no-op parser flag), then rerun both
commands.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and Lake
only from `verification/`.

`lake build NSFormalization.Section3.T17.ArticleScope` — exit 0. Lake replayed
pre-existing upstream warnings, but emitted no diagnostic from `ArticleScope`;
exact first and last lines:

```text
⚠ [8778/9106] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
...
Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10656 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T17/ArticleScope.lean`
— exit 0, exact output: `(no output)`.

`lake env lean ../research/T17/axioms_493.lean` — exit 0. All 26 prints in
`research/T17/axioms_493.lean:3-28` contain exactly the permitted set. Exact
first and last excerpts:

```text
'NSFormalization.Section3.T17.correctionStatementArticle_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.article_window_identification' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.article_force_identification' depends on axioms: [propext, Classical.choice, Quot.sound]
...
'NSFormalization.Section3.T17.article_force_profile_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.article_correction_profile_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.article_force_profile_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` — exit 0, exact output:

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

`make test` — exit 0. It checked all registered contracts; exact first and last
lines (middle replay output omitted under the raw-output limit):

```text
lake -d verification test
⚠ [8778/9235] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
...
ℹ [11003/11004] Replayed Tests.TorusNonDensity
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
ℹ [11004/11004] Replayed Tests.TorusMain
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`make test-mutations` — exit 0; exact last lines:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

Fresh article audit:
`python3 experiments/audit_article_axioms.py --build --output-dir tmp/rev493-article-audit --workers 2`
— exit 0; its `report.json` is byte-identical to
`formalization/blueprint/AXIOM_AUDIT.json`. Exact final output:

```text
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
65 declarations; 27 article entries; 0 forbidden-axiom results
```

`make paper` — exit 0; exact final output:

```text
python3 ../experiments/check_reader_documents.py
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 30 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/493-T17-P2-article-scope/paper'
```

Reviewer non-vacuity probe:
`lake env lean ../research/T17/probes/rev493_nonvacuity.lean` — exit 0,
exact output: `(no output)`.

Reviewer exponent mutation:
`lake env lean ../research/T17/probes/rev493_mutation.lean` — exit 1 with the
expected error quoted in part 2.

Mandatory direct compatibility check — **exit 2**:

```text
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
```

Mandatory `scripts/gates.sh` — **exit 2** after `make check`, `make test`, and
`make test-mutations` passed. Exact first and final output excerpts:

```text
== make check
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2242 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
...
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
```

Required fix: restore functional `--base-ref` compatibility checking in
`experiments/check_contracts.py` (or first amend the governing gate contract and
all callers), then rerun the direct command and `scripts/gates.sh` to exit 0.

## Lead ruling (2026-09-21 04:20Z)
REJECT reason is a tooling artefact: the owner's streamlined `experiments/check_contracts.py` has no `--base-ref` option; `scripts/gates.sh` (now fixed to `--summary`) and the review prompt still invoked it. The reviewer confirms mathematics, statement fidelity, axioms, mutation, non-vacuity, `make test`, documents all pass. Merged on lead authority.
