ACCEPT

## 1. What the lane claims

Independent read-only review of lane 506. Read CLAUDE.md, the lane-review skill, the first 40 lines of LESSONS, COMMON_PHASE5, ASSESSMENT, P6_SPLIT, REPORT_504, REPORT_506, ATTEMPTS_B3, and the B1/B3 modules. User instructions override the skill's obsolete model, installation, and `--base-ref` directions. No tracked implementation, record, or git state was changed. The pre-existing untracked brief and tight-height probe were left intact; this reviewer added the sign-mutation probe and this review.

`research/P21/REPORT_506.md:7` claims six abstract real-analysis results, not a Navier–Stokes restart theorem. This matches the brief. The citation at `formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean:9` is accurate: opening `paper/revised/sections/02-preliminaries.tex:149` through 182 with `sed -n` confirms that lines 153–156 give finite squared-H² time integral implies smooth extension. Lines 178–182 use high-order bounds to restart; they do not display an H¹-uniform clause.

## 2. What is in Lean

Below, B3 means `formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean`. Every claimed exported theorem exists; the following records the actual assumptions as well as the conclusions.

| Declaration | Checked statement and fidelity |
| --- | --- |
| `enstrophy_integrated_of_bound`, B3:22 | For c>0, C≥0, a≤b, continuous Y on Icc, differentiable Y on Ioo, integrable Z on Icc, Y(a)≤K, Y(b)≥0, interior Y≤M, and the stated cubic differential inequality, returns `∫ a..b Z ≤ (K+C(1+M)^3(b-a)+CF(b-a))/c`. No unnecessary nonnegativity of Z or F is imposed on this standalone result. |
| `enstrophy_reciprocal_barrier`, B3:50 | For c,C,F≥0 and a≤b, with endpoint continuity, interior differentiability, Y≥0 on Icc, Z≥0 on Ioo and the differential inequality, returns precisely `1/(1+Y a)^2 - 2*C*(1+F)*(b-a) ≤ 1/(1+Y b)^2`. |
| `enstrophy_uniform_barrier`, B3:85 | For c,C>0 and K,F≥0, `∃ d>0, ∃ M, M=2*(1+K)-1 ∧ ∀ a S Y Z, ...`. All interval/function quantifiers follow both constants. The hypotheses are S≤d, endpoint continuity, interior differentiability, nonnegative Y and Z on their stated sets, initial bound, and the differential inequality; the conclusion is Y≤M on Icc. B3:95 explicitly chooses `d=1/(4*C*(1+F)*(1+K)^2)`. The formula for d is the proof witness, not an equality exported in the existential signature; the report accurately describes a choice. |
| `enstrophy_endpoint_lintegral`, B3:124 | For B in ℝ≥0∞, bounds of `∫⁻ Ico a s, ofReal (Z t)` for every s<b imply the identical bound on Ico a b. No measurability or positivity assumption on real Z is needed because the integrand is ofReal Z. This alone does not assert finiteness when B=∞. |
| `enstrophy_endpoint_integral`, B3:146 | Assumes a≤b, B≥0, globally measurable Z, nonnegative Z on Ico a b, and compact integrability plus real integral bounds for every a≤s<b. Returns the conjunction `IntegrableOn Z (Icc a b) ∧ (∫ a..b Z)≤B`, exactly as claimed. |
| `enstrophy_uniform_barrier_and_dissipation`, B3:174 | Same existential order as the barrier, with 0≤S≤d and explicit compact integrability of Z. Returns both the closed-interval height and `∫ a..a+S Z ≤ (K+C(1+M)^3*S+C*F*S)/c`. |

Lead checkpoints:

1. Uniformity is genuine (B3:87–98, 176–188): neither d nor M can depend on restart time, length, Y, or Z. Their displayed choices only depend on C,K,F, which is allowed. Strict positivity follows from C>0 and K,F≥0.
2. Differentiability is only on Ioo (B3:26,54,90,179); no integrability of Y′ occurs. The proof uses the actual Mathlib one-sided FTC at `verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1068`, opened with sed: it requires an integrable upper bound φ, not an integrable derivative. B3:32–38 constructs φ from a constant and cZ.
3. Endpoint integrability is proved before conversion to a real bound (B3:165–171). `ofReal B < ∞` supplies finiteness; `toReal_mono` is used with `ofReal_ne_top`. There is no use of `⊤.toReal=0`. The singleton endpoint is transferred by `integrableOn_Icc_iff_integrableOn_Ico`.
4. Non-vacuity is already present in `research/P21/probes/b3_closes.lean:8`, :24–70, and :73. The cubic solution really satisfies `HasDerivAt cubicSolution ((1+cubicSolution t)^3) t` for t<1/2, and continuity, nonnegativity, initial value and differential inequality are proved explicitly. Since d>0, `S=min d (1/4)/2` is strictly positive and allowed by the probe; this is not an empty-interval witness. Constants and zero dissipation also instantiate the combined theorem. Negative S in the standalone theorem merely extends the valid statement to empty intervals; it does not restrict positive intervals.
5. All six axiom lists are exactly `[propext, Classical.choice, Quot.sound]`, including the wrapped output for the last theorem. B3:1–4 imports only Mathlib. `research/P21/axioms_b3.lean:4` onward prints and checks each theorem.

The directed-union proof is also supported by the actual library statement: `verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:646` requires countability and directedness, with no measurability hypothesis. B3:127–141 supplies the rational exhaustion and directedness.

Hygiene: no forbidden proof tokens or maxHeartbeats settings in B3 or the worker's closing probe. No existing Lean module is modified in the requested three-dot diff: B3 and inherited B1 are added files. `formalization/blueprint/entrypoints.json:52` registers B3. No verification files, contracts, proof_graph status, or guide coverage changes appear. `formalization/blueprint/proof_graph.json:78–80` still has L21_H1 Partial. The generated graph/audit changes are disclosed at REPORT_506:44–46. Git warns of multiple merge bases, so this review also inspected name-status output rather than inferring file creation solely from names.

## 3. Gaps

No B3 mathematical or Lean defect found. The real endpoint theorem's local-integrability premise is an honest and necessary qualification (B3:143–150; REPORT_506:56–61). Bounds on Lean's totalized real integral of a nonintegrable function cannot establish finiteness. The lintegral alternative addresses that distinction. Global measurability and B≥0 are explicit, consistent assumptions, not concealed restrictions.

For every residual in REPORT_506:63–66, searched the entire Section4 tree with `grep -rnE 'H1|H¹|restart|Restart|extendsBeyond|force.*(bound|cap)|[Ii]ntegrableOn|[Dd]ifferentiableAt' formalization/NSFormalization/Section4` (331 matching lines). The residual is assembly, not absence of all ingredients:

- Classical regularity and compact integrability have existing infrastructure in `A04/RestartFixedForce.lean:146` and :202–211. B1's `EnstrophyInequality.lean:469` gives its differential estimate only on subintervals strictly inside (0,T), with exactly the three norm bridges recorded in P6_SPLIT. B4 must connect these results to the abstract Y,Z, including the initial endpoint; B3 does not claim that connection.
- Force bounds already exist: `A04/Forcing.lean:160` proves a finite compact H¹ force cap; `A04/RestartFixedForce.lean:21` bounds translated force windows. These must be adapted to the common real force cap in B3. The report correctly says “supply”, not “no force bound exists”.
- The H² criterion already exists at `A04/ShiftedExtension.lean:247`, and its :256 theorem handles maximality from locally finite H² integrals. Read the actual statements with sed. The uniform restart result at :236 instead assumes an H⁷ bound. `A04/RestartFixedForce.lean:15` likewise uses order 7, while `A01/Continuation.lean:249` requires q≥6 and order q+1. None closes the smooth H¹-ball common-window/restart assembly claimed as remaining B4/B5 work.

The sole failing gate is inherited tooling: `experiments/test_contract_policy.py:31–34` selects C35_FULL, sets it Closed, and expects a Partial-coverage contradiction. Read-only `git show ef2cc079^:...` confirms both this test and C35_FULL's already-Closed status predate B3. As directed by the lead, this is not a lane defect. The reported lane-509 integration fix need not be copied into this read-only worktree.

Negative checks: the pre-existing `research/P21/probes/rev506_tight_height_mutation.lean:14` changes M=2(1+K)−1 to M=K; its application fails with the expected type mismatch at :23. More substantively, this reviewer added `research/P21/probes/rev506_sign_mutation.lean:58`, copying the original reciprocal proof unchanged but replacing the conclusion's minus sign by plus. It fails at :81 with `linarith failed to find a contradiction`. No argument or hypothesis was dropped. The mutated statement is false even for Y=Z=0, c=C=1, F=0, a=0, b=1: it would require 3≤1.

Required lane fixes: none.

## 4. Commands and results

All Lean shells sourced `. scripts/lean-env.sh` and exported `LEAN_NUM_THREADS=6`. Direct lake commands ran from verification; the owner's Makefile uses `lake -d verification test`. No install, git checkout/reset/stage/commit, or source repair was performed. Outputs below are exact, with no more than the first and last 40 lines retained for any command.

`lake build NSFormalization.Section4.A04.EnstrophyBarrier`: exit 0, no module warning/error (Lake itself prints its success summary):

```text
Build completed successfully (2653 jobs).
```

`lake env lean ../formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean`: passed, zero output.

`lake env lean ../research/P21/probes/b3_closes.lean`: passed, zero output.

`lake env lean ../research/P21/axioms_b3.lean`: passed:

```text
'NSFormalization.Section4.A04.enstrophy_integrated_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_integrated_of_bound: checked; standard logical axioms only
'NSFormalization.Section4.A04.enstrophy_reciprocal_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_reciprocal_barrier: checked; standard logical axioms only
'NSFormalization.Section4.A04.enstrophy_uniform_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_uniform_barrier: checked; standard logical axioms only
'NSFormalization.Section4.A04.enstrophy_endpoint_lintegral' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_endpoint_lintegral: checked; standard logical axioms only
'NSFormalization.Section4.A04.enstrophy_endpoint_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_endpoint_integral: checked; standard logical axioms only
'NSFormalization.Section4.A04.enstrophy_uniform_barrier_and_dissipation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_uniform_barrier_and_dissipation: checked; standard logical axioms only
```

`lake env lean ../research/P21/probes/rev506_sign_mutation.lean`: exit 1, expected:

```text
../research/P21/probes/rev506_sign_mutation.lean:81:2: error: linarith failed to find a contradiction
c C F a b : ℝ
Y Z : ℝ → ℝ
hc : 0 ≤ c
hC : 0 ≤ C
hF : 0 ≤ F
hab : a ≤ b
hY : ContinuousOn Y (Icc a b)
hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ Y t
hn : ∀ t ∈ Icc a b, 0 ≤ Y t
hZ : ∀ t ∈ Ioo a b, 0 ≤ Z t
hi : ∀ t ∈ Ioo a b, deriv Y t + c * Z t ≤ C * (1 + Y t) ^ 3 + C * F
hp : ∀ t ∈ Icc a b, 0 < 1 + Y t
hcont : ContinuousOn (fun t => -(1 / (1 + Y t) ^ 2)) (Icc a b)
hder : ∀ t ∈ Ioo a b, HasDerivAt (fun t => -(1 / (1 + Y t) ^ 2)) (2 * deriv Y t / (1 + Y t) ^ 3) t
hbound : ∀ t ∈ Ioo a b, 2 * deriv Y t / (1 + Y t) ^ 3 ≤ 2 * C * (1 + F)
h : -(1 / (1 + Y b) ^ 2) - -(1 / (1 + Y a) ^ 2) ≤ (b - a) * (2 * C * (1 + F))
a✝ : 1 / (1 + Y b) ^ 2 < 1 / (1 + Y a) ^ 2 + 2 * C * (1 + F) * (b - a)
⊢ False
failed
```

`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean research/P21/probes/b3_closes.lean`: zero matches. `git diff --check`: exit 0, zero output.

`git diff --name-only origin/erenup/core...HEAD`:

```text
warning: origin/erenup/core...HEAD: multiple merge bases, using 79e9af5bc4c6f4150e7ddefb240c9b4259e75c8d
formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean
formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean
formalization/blueprint/AXIOM_AUDIT.json
formalization/blueprint/DEPENDENCY_GRAPH.md
formalization/blueprint/entrypoints.json
research/P21/ATTEMPTS_B1.md
research/P21/ATTEMPTS_B3.md
research/P21/P6_SPLIT.md
research/P21/REPORT_504.md
research/P21/REPORT_506.md
research/P21/axioms_b1.lean
research/P21/axioms_b3.lean
research/P21/probes/b1_closes.lean
research/P21/probes/b3_closes.lean
```

Although verification was untouched, both `make test` and `make test-mutations` were rerun and passed (exit 0); replayed warnings are from existing modules. Their exact output excerpts follow.

`make test`: first 40 lines:

```text
lake -d verification test
⚠ [8778/8865] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9357/9623] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9358/9623] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9881/10938] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

Last 40 lines:

```text
ℹ [10943/11015] Replayed Tests.PeriodicInsertionV2
info: Tests/PeriodicInsertionV2.lean:11:0: Contract BlowupDensity.Tests.checkedPeriodicInsertionV2: checked; standard logical axioms only
info: Tests/PeriodicInsertionV2.lean:12:0: Contract NSFormalization.Section3.T19.periodicInsertion_from_data: checked; standard logical axioms only
info: Tests/PeriodicInsertionV2.lean:13:0: Contract NSFormalization.Section3.T19.At.velocityDifference_support: checked; standard logical axioms only
ℹ [10951/11015] Replayed Tests.MultipleRegions
info: Tests/MultipleRegions.lean:18:0: Contract BlowupDensity.Tests.checkedMultipleRegions: checked; standard logical axioms only
ℹ [10975/11015] Replayed Tests.CompletedDensity
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
ℹ [10979/11015] Replayed Tests.Correction3V2
info: Tests/Correction3V2.lean:10:0: Contract BlowupDensity.Tests.checkedCorrection3V2: checked; standard logical axioms only
info: Tests/Correction3V2.lean:12:0: Contract BlowupDensity.Bindings.Correction3.correctionArticle_of_packet: checked; standard logical axioms only
ℹ [10980/11015] Replayed Tests.Scaling3
info: Tests/Scaling3.lean:15:0: Contract BlowupDensity.Tests.checkedScaling3: checked; standard logical axioms only
info: Tests/Scaling3.lean:45:0: Contract BlowupDensity.Tests.checkedScaling3Packet: checked; standard logical axioms only
info: Tests/Scaling3.lean:78:0: Contract BlowupDensity.Tests.scaling3_source_nonzero: checked; standard logical axioms only
info: Tests/Scaling3.lean:79:0: Contract BlowupDensity.Tests.scaling3_periodized_nonzero: checked; standard logical axioms only
ℹ [10984/11015] Replayed Tests.AffineVariation
info: Tests/AffineVariation.lean:34:0: Contract BlowupDensity.Tests.checkedAffineVariation: checked; standard logical axioms only
info: Tests/AffineVariation.lean:41:0: Contract BlowupDensity.Tests.checkedAffineVariationStatement: checked; standard logical axioms only
ℹ [10986/11015] Replayed Tests.LocalTheoryV2
info: Tests/LocalTheoryV2.lean:26:0: Contract BlowupDensity.Tests.checkedLocalTheoryV2: checked; standard logical axioms only
ℹ [10987/11015] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10988/11015] Replayed Tests.TorusLocalTheory
info: Tests/TorusLocalTheory.lean:26:0: Contract BlowupDensity.Tests.checkedTorusLocalTheory: checked; standard logical axioms only
ℹ [10994/11015] Replayed Tests.ForceClasses
info: Tests/ForceClasses.lean:16:0: Contract BlowupDensity.Tests.checkedForceClasses: checked; standard logical axioms only
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

`make test-mutations`: first 40 lines:

```text
python3 experiments/test_contract_mutations.py
⚠ [8778/9235] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9357/10296] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9358/10296] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9881/10296] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

Last 40 lines:

```text
info: Tests/MultipleRegions.lean:18:0: Contract BlowupDensity.Tests.checkedMultipleRegions: checked; standard logical axioms only
ℹ [10975/11015] Replayed Tests.CompletedDensity
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
ℹ [10979/11015] Replayed Tests.Correction3V2
info: Tests/Correction3V2.lean:10:0: Contract BlowupDensity.Tests.checkedCorrection3V2: checked; standard logical axioms only
info: Tests/Correction3V2.lean:12:0: Contract BlowupDensity.Bindings.Correction3.correctionArticle_of_packet: checked; standard logical axioms only
ℹ [10980/11015] Replayed Tests.Scaling3
info: Tests/Scaling3.lean:15:0: Contract BlowupDensity.Tests.checkedScaling3: checked; standard logical axioms only
info: Tests/Scaling3.lean:45:0: Contract BlowupDensity.Tests.checkedScaling3Packet: checked; standard logical axioms only
info: Tests/Scaling3.lean:78:0: Contract BlowupDensity.Tests.scaling3_source_nonzero: checked; standard logical axioms only
info: Tests/Scaling3.lean:79:0: Contract BlowupDensity.Tests.scaling3_periodized_nonzero: checked; standard logical axioms only
ℹ [10984/11015] Replayed Tests.AffineVariation
info: Tests/AffineVariation.lean:34:0: Contract BlowupDensity.Tests.checkedAffineVariation: checked; standard logical axioms only
info: Tests/AffineVariation.lean:41:0: Contract BlowupDensity.Tests.checkedAffineVariationStatement: checked; standard logical axioms only
ℹ [10986/11015] Replayed Tests.LocalTheoryV2
info: Tests/LocalTheoryV2.lean:26:0: Contract BlowupDensity.Tests.checkedLocalTheoryV2: checked; standard logical axioms only
ℹ [10987/11015] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10988/11015] Replayed Tests.TorusLocalTheory
info: Tests/TorusLocalTheory.lean:26:0: Contract BlowupDensity.Tests.checkedTorusLocalTheory: checked; standard logical axioms only
ℹ [10994/11015] Replayed Tests.ForceClasses
info: Tests/ForceClasses.lean:16:0: Contract BlowupDensity.Tests.checkedForceClasses: checked; standard logical axioms only
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
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2`: exit 0. Only ignored audit output was refreshed; the tracked AXIOM_AUDIT.json was not rewritten. Exact output:

```text
NSFormalization.Section3.T17.ArticleScope: 9 declarations checked
NSFormalization.Section3.T21.MainAssembly: 30 declarations checked
Bindings.ForceAmplitude: 6 declarations checked
Bindings.CompletedDensity: 8 declarations checked
Bindings.PeriodicInsertionV2: 2 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
Bindings.AffineVariation: 1 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
69 declarations; 27 article entries; 0 forbidden-axiom results
```

`make check` after the fresh audit: exit 2. The first run had the same failure (11 tests in 0.003s). Packaging and the registry pass; no stale-source audit error occurs. Exact retry output:

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
  File "/data_8T/ping/blowup_density/.claude/worktrees/506-P21-B3-ode-barrier/experiments/test_contract_policy.py", line 34, in test_recoloring_a_missing_clause_cannot_hide_whole_statement_partial
    with self.assertRaisesRegex(AssertionError, 'disagrees with whole-statement coverage'):
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: AssertionError not raised

----------------------------------------------------------------------
Ran 11 tests in 0.003s

FAILED (failures=1)
make: *** [Makefile:6: check] Error 1
```

Verdict: ACCEPT. Required fixes: none. The inherited C35_FULL policy-test repair belongs to the integration branch, as stated in the lead instructions.
