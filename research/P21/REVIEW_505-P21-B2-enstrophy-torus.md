ACCEPT-WITH-NOTES

## 1. What the lane claims

The operative claim is the continuation section of `REPORT_505.md`, not its
preserved historical partial report: the report explicitly says that the
continuation supersedes the earlier status (`research/P21/REPORT_505.md:3-8`).
It claims that B2 proves the general periodic inhomogeneous enstrophy
differential inequality, conditional only on the three κ=1 torus norm bridges,
while P6 / `L21_H1` remains Partial.

That scope is faithful to the source and the brief:

- Proposition 2.1 states maximal smooth existence and the squared-H²
  continuation criterion at `paper/revised/sections/02-preliminaries.tex:147-156`;
  its proof explicitly retains nonzero periodic mean at
  `paper/revised/sections/02-preliminaries.tex:165-168`.
- This lane is an internal step toward the separate H¹-uniform restart
  obligation, not a closure of Proposition 2.1. The blueprint still records
  `L21_H1` as Partial at `formalization/blueprint/proof_graph.json:78-90`.
- The report's constants and target are recorded at
  `research/P21/P6_SPLIT.md:63-70`, and the three allowed bridge statements are
  exactly those at `research/P21/P6_SPLIT.md:76-86`.

The report says there are 30 proved theorems. All 30 exist. Their declaration
anchors, in source order, are:

- analytic/scalar layer: `formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:30`,
  `:50`, `:71`, `:96`, `:112`, `:128`, `:138`, `:178`, `:194`, `:216`;
- cutoff/localization layer: the same file at `:235`, `:273`, `:279`, `:284`,
  `:291`, `:301`, `:319`, `:356`, `:379`, `:420`;
- physical/final layer: the same file at `:455`, `:472`, `:483`, `:508`,
  `:546`, `:562`, `:602`, `:658`, `:696`, `:723`.

The two reported explicit constants also exist with the claimed definitions:
`velocitySixConstT` at
`formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:416-417`
and `convectionConstT` at the same file's `:599`.

## 2. What is in Lean

### Final statements and hypotheses

`enstrophy_differential_of_norm_bridgesT` has precisely the three bridge
inputs at
`formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:658-673`:

1. the full H¹ equality on every `s ∈ Ioo 0 T` (`:661-663`);
2. the H² upper bound with coefficient `2` on gradient energy (`:665-667`);
3. the gradient L² carrier bound (`:668-669`).

`enstrophy_differentialT` repeats exactly that κ=1 interface and combines the
two RHS coefficients into the reported common
`Cν = (2*C)^4/(ν/2)^3 + (1+ν) + (1+2/ν)` at
`formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:696-719`.
`enstrophy_differential_on_IccT` assumes `0 < r`, `s < T`, the same H¹ bridge
on `Ioo 0 T`, and the other two bridges on `Icc r s`, then concludes the
inequality at every point of that interval
(`formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:723-743`).
There is no fourth norm, nonlinear, differential, smallness, initial-class, or
endpoint hypothesis.

The interval theorem does not state `r ≤ s`, so it also permits empty `Icc`s,
but its proof is pointwise and applies unchanged to every nonempty interval;
it does not rely on emptiness. The supplied probe instantiates an actual
`ClassicalSolutionT 1 0 0 2` on the nonempty interval `[1/2,1]` and discharges
all three bridges (`research/P21/probes/b2_closes.lean:83-127`). Thus the final
interface is not vacuous. The same probe separately permits positive ordinary
energy with zero spatial derivatives (`research/P21/probes/b2_closes.lean:18-25`).

There is no `⊤.toReal = 0` loophole in the use made here. A
`ClassicalSolutionT` supplies smooth periodic slices and integer-order Sobolev
data (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-299`),
and the actual witness proves the bridge premises directly. The extended norm
uses the inhomogeneous weight `1 + 4π²|k|²`, whose zero-mode weight is one
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:66-69,94-120`).
The physical quantities are exactly squared `toReal` periodic L² norms
(`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:90-103`).
Consequently the ordinary L² term and mean are retained in both `Y` and the H²
comparison.

### Proved cancellations and estimates

- Periodic convection cancellation is a theorem, not an input:
  `periodicPairing_convection_zeroT` reduces to the cube transport identity at
  `formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:471-480`.
- Pressure cancellation is proved upstream frequency-by-frequency using
  solenoidality at
  `formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:887-916`, and
  the resulting pressure-free classical identity is stated at
  `formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:996-1010`.
  The lane then derives its physical identity at
  `formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:508-543`.
- The full order-one dissipation is proved to be gradient plus Laplacian energy
  at `formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:483-504`.
- The velocity L⁶ estimate retains both velocity and gradient L² terms at
  `formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:419-449`;
  convection is then bounded in the full inhomogeneous H¹ energy at `:602-654`.
- T20's absorbed theorem really does require critical smallness
  (`formalization/NSFormalization/Section3/T20/H1Energy.lean:395-417`), but this
  lane never invokes it. It uses only unconditional derivative, Parseval,
  regularity, and measurability lemmas from T20.

The module is registered in the compiled proof closure at
`formalization/blueprint/entrypoints.json:17`. The axiom audit file has one
`#print axioms` and one `checkAxioms` for each of the 30 exports
(`research/P21/axioms_b2.lean:4-64`); every result is exactly
`[propext, Classical.choice, Quot.sound]`.

### Independent mutation

The reviewer probe keeps a satisfiable instance of every scalar premise and
first checks the advertised `c=1` conclusion
(`research/P21/probes/rev505_dissipation_mutation.lean:5-15`). It then changes
the main dissipation constant to `c=5`, without dropping an argument. The
mutated conclusion normalizes to the false assertion `3 ≤ 2`, and
`#guard_msgs` verifies the expected `⊢ False` failure
(`research/P21/probes/rev505_dissipation_mutation.lean:17-26`). This is a
substantive constant mutation and is independent of the worker's sign/removal
mutation at `research/P21/probes/b2_closes.lean:129-145`.

## 3. Gaps

There is no remaining B2 mathematical gap. B3 still owes the ODE barrier and
endpoint passage; B4/B5 owe lifespan/restart assembly. The report correctly
does not recolor `L21_H1`.

The one named B4 reconciliation gap is honest: the report does not claim
`periodicHessianEnergy z = laplacianSqT z`. The required whole-tree searches

```text
grep -rn "periodicHessianEnergy" formalization/NSFormalization/Section4
grep -rn "laplacianSqT" formalization/NSFormalization/Section4
```

both returned exit 1 with zero output. No such declaration is present in the
current Section4 tree. The obligation and the other two carrier conversions
are stated at `research/P21/P6_SPLIT.md:96-117`, without being misrepresented
as results of this lane.

Hygiene is otherwise clean: source/probe searches found no
`sorry`/`admit`/`axiom`/`native_decide` and no `maxHeartbeats` override. The
required `git diff --name-only origin/erenup/core...HEAD` lists the two new B1/B2
proof modules plus records/blueprint files; `git diff --diff-filter=M ... --
formalization/NSFormalization` returns no paths, so no pre-existing Lean module
was modified. There is no `verification/` diff. The pre-existing untracked lane
brief remains unmodified.

The note preventing a fully clean ACCEPT is output hygiene. Direct Lean exits
0 but emits six warnings from the new module instead of the required zero
output. Exact one-line fixes:

1. At `formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:93`,
   `:125`, `:132`, and `:543`, replace the tactic combinator `<;>` by `;`.
2. At the same file's `:466`, remove `Pi.add_apply` from the `simp only` list.
3. At the same file's `:502`, remove `torusGradientEnergyT` from the
   `simp only` list.
4. Probe-only cleanup: at `research/P21/probes/b2_closes.lean:77`, replace
   `by intros; simp [...]` with `by simp [...]`.

These are linter-only changes; they do not affect the verdict on mathematics or
axioms. The `make check` failure is the lead's documented inherited
`C35_FULL` fixture defect, not a lane defect: the fixture sets an already-Closed
node to Closed at `experiments/test_contract_policy.py:29-35`, while the node is
already Closed at `formalization/blueprint/proof_graph.json:179-183`.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.

### Module build

`lake build NSFormalization.Section3.T11.EnstrophyInequality` exited 0. The raw
output had 489 lines; under the raw-output limit, its exact lane-local tail was:

```text
⚠ [10656/10656] Replayed NSFormalization.Section3.T11.EnstrophyInequality
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:93:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:125:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:132:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:466:66: This simp argument is unused:
  Pi.add_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [velocityCoeffT, NSFormalization.Section4.C01.lift]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:502:13: This simp argument is unused:
  torusGradientEnergyT

Hint: Omit it from the simp argument list.
  [apply] simp only [Real.rpow_one, T20.h1FreqEnergy]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:543:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Build completed successfully (10656 jobs).
```

### Direct module typecheck

`lake env lean ../formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean`
exited 0 but was not 0-output. Its exact output was the same six warnings:

```text
../formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:93:21: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:125:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:132:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:466:66: warning: This simp argument is unused:
  Pi.add_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [velocityCoeffT, NSFormalization.Section4.C01.lift]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:502:13: warning: This simp argument is unused:
  torusGradientEnergyT

Hint: Omit it from the simp argument list.
  [apply] simp only [Real.rpow_one, T20.h1FreqEnergy]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:543:21: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

### Worker and reviewer probes

`lake env lean ../research/P21/probes/b2_closes.lean` exited 0. Its declarations
and final signatures printed as expected; its exact final output was:

```text
../research/P21/probes/b2_closes.lean:77:23: warning: Unused tactic linter: `intros` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
```

`lake env lean ../research/P21/probes/rev505_dissipation_mutation.lean` exited
0 with zero output. The guarded expected error is `⊢ False` at probe lines
20-22.

### Axioms

`lake env lean ../research/P21/axioms_b2.lean` exited 0. It printed 30 axiom
sets and 30 successful `checkAxioms` results. The exact first and last entries
were:

```text
'NSFormalization.Section3.T11.inhomogeneousEnergyIdentityT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.inhomogeneousEnergyIdentityT: checked; standard logical axioms only
'NSFormalization.Section3.T11.lintegral_convection_holder_632T' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Contract NSFormalization.Section3.T11.lintegral_convection_holder_632T: checked; standard logical axioms only
...
'NSFormalization.Section3.T11.enstrophy_differential_on_IccT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.enstrophy_differential_on_IccT: checked; standard logical axioms only
'NSFormalization.Section3.T11.enstrophy_differential_of_norm_bridgesT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Contract NSFormalization.Section3.T11.enstrophy_differential_of_norm_bridgesT: checked; standard logical axioms only
```

Every omitted middle entry had exactly the same three-axiom set; TestSupport
would fail the command on any additional axiom.

### Article audit and owner checks

`python3 experiments/audit_article_axioms.py --build --output-dir
tmp/article-audit --workers 2` exited 0 with exact output:

```text
NSFormalization.Section3.T17.ArticleScope: 9 declarations checked
NSFormalization.Section3.T21.MainAssembly: 30 declarations checked
Bindings.CompletedDensity: 8 declarations checked
Bindings.ForceAmplitude: 6 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
Bindings.PeriodicInsertionV2: 2 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
69 declarations; 27 article entries; 0 forbidden-axiom results
```

After that audit, `make check` exited 2 with exact output:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2259 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 32,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.F.........
======================================================================
FAIL: test_recoloring_a_missing_clause_cannot_hide_whole_statement_partial (__main__.ArticleProofCoverage.test_recoloring_a_missing_clause_cannot_hide_whole_statement_partial)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/505-P21-B2-enstrophy-torus/experiments/test_contract_policy.py", line 34, in test_recoloring_a_missing_clause_cannot_hide_whole_statement_partial
    with self.assertRaisesRegex(AssertionError, 'disagrees with whole-statement coverage'):
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: AssertionError not raised

----------------------------------------------------------------------
Ran 11 tests in 0.003s

FAILED (failures=1)
make: *** [Makefile:6: check] Error 1
```

This is exactly the lead-noted inherited failure; the blueprint and contract
summary steps passed.

### Test, mutation, and paper gates

`make test` exited 0; the raw log had 540 lines. Exact last lines:

```text
ℹ [11010/11015] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:17:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [11011/11015] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:18:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [11012/11015] Replayed Tests.BoundedDomainNorm
info: Tests/BoundedDomainNorm.lean:28:0: Contract BlowupDensity.Tests.checkedBoundedDomainNorm: checked; standard logical axioms only
info: Tests/BoundedDomainNorm.lean:33:0: Contract BlowupDensity.Tests.checkedBoundedDomainNormStatement: checked; standard logical axioms only
ℹ [11013/11015] Replayed Tests.PeriodicInsertion
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
ℹ [11014/11015] Replayed Tests.TorusNonDensity
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
ℹ [11015/11015] Replayed Tests.TorusMain
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`make test-mutations` exited 0; the raw log had 545 lines. Exact tail:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`make paper` exited 0 with exact substantive output:

```text
Latexmk: Nothing to do for 'blowup_density_revised.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/505-P21-B2-enstrophy-torus/output/pdf/blowup_density_revised.pdf) are up-to-date
Latexmk: Nothing to do for 'formalization_guide.tex'.
Latexmk: All targets (/data_8T/ping/blowup_density/.claude/worktrees/505-P21-B2-enstrophy-torus/output/pdf/formalization_guide.pdf) are up-to-date
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 32 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
```

Finally, `git diff --check origin/erenup/core...HEAD` and `git diff --check`
both exited 0 with no diff errors. `git status --short` showed only the
pre-existing untracked lane brief and this reviewer's permitted
`rev505_dissipation_mutation.lean` before the review report was written.

---
**Lead ruling (2026-09-21 05:42Z):** merged as-is. All notes are linter-style (`<;>` → `;` at module lines 93/125/132/543, unused simp argument at 466, unused `torusGradientEnergyT` at 502, probe line 77) with no mathematical or axiom content; lane 508 (B4-𝕋³) already builds on this module, so the cosmetic edits are deferred to the closing lane 511 checklist ("deferred reviewer style notes"), to be applied in one pass.
