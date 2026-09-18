ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed branch erenup/400-T12-U5-gradient-l6 at 44e8bf31 (proof commit 240b1d55), against origin/erenup/integration-section3 using the requested three-dot diff. Read CLAUDE.md, .claude/skills/lane-review/SKILL.md, logs/LESSONS.md:1–40, T12_SPLIT.md §0/U5, REPORT_400.md, REPORT_365.md, REPORT_366.md, REPORT_377.md, and the cited sources. research/T12/ATTEMPTS_U4.md is absent; its requested pin-specific precautions were checked against the actual proof. No installation was needed: the existing pinned environment builds successfully.

research/T12/REPORT_400.md:9–34 claims the exact U5 field with a fixed positive constant, proved by route (c), with no named input or residual:
```lean
theorem gradientLSix :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)

def Csix : ℝ :=
  343 * NSFormalization.Section4.A05.gradientL6Const * leibnizConst * (1 + 2 * hTwoConst)
```

## 2. What is in Lean

Here G denotes formalization/NSFormalization/Section3/T12/GradientLSix.lean. All references were opened, not inferred from the report.

1. **Statement fidelity: PASS.** G:641–644 is the claimed statement verbatim, matching research/T12/probes/api_on_canonical.lean:184–187. G:614 and G:617 supply precisely the reported constant and positivity. paper/sections/appendix-b-embeddings.tex:26–32 displays the gradient L⁶/Laplacian L² inequality; :109–110 permits constants depending on the fixed domain and norm conventions. paper/sections/03-torus.tex:467–477 uses that estimate in the H¹ energy argument. The smooth-core scope is exactly the brief's requested API.

2. **Definitions and hypotheses: PASS.** MeanZeroCalculus.lean:66, :71, :84, :89 (same Section3/T12 directory) use genuine smooth periodic fields, the Haar eLpNorm, the Frobenius gradient tensor, and the componentwise Laplacian. Section3/T10/PeriodicData.lean:157 defines physical mean zero as meanT v = 0. The main theorem has only v, smooth periodicity and mean zero; there is no hidden named estimate, empty interval, arbitrary measure, or frequency cutoff. Both main hypotheses are used (G:675, :679, :693–694). Csix is independent of v, strictly positive and finite as a real number. G:539–541 converts only the finite exponent 2 to a real number, never an infinite norm to zero.

3. **Reported analytic lemmas: PASS.** The two lower-order inequalities are exactly at G:101 and G:167, with the intermediate homogeneous/H² comparison at G:136. SpectralGap.lean:127 really takes a real multiplier; FourierEmbeddings.lean:127, :165 give the reported hTwoConst and mean-zero Laplacian estimate. Section3/T10/ForcePaths.lean:357 and CutoffGagliardo.lean:59 justify the gradient homogeneous-norm identification and deletion of the mean-free projection. No new premise is introduced.

4. **Localization and registered theorem: PASS.** G:193, :202, :217, :232 establish the product rules and doubled cross term; G:273 proves every jet of the cutoff product is L². Section4/A05/SmoothJets.lean:44 defines exactly that SmoothL2 hypothesis; Section4/A05/GradientL6.lean:45, :52, :64 have the stated tensor, constant and whole-space inequality. verification/Bindings/GradientL6.lean:22–46 bridges these definitions by rfl and registers that theorem. HaarCube.lean:190, Cutoff.lean:60, G:558 and G:664–675 implement the cube transfer, neighborhood equality and measure monotonicity. The cutoff plateau contains the nonempty unit cube, including its boundary.

5. **Majorant and tiling: PASS, with the prose correction below.** G:269, :289, :304, :312 define the reported derivative bounds and leibnizConst; G:320 proves its pointwise estimate. G:417 establishes vanishing of the localized Laplacian outside the radius-three ball. G:478 inserts the ball indicator, G:496 folds the integral by periodicity, and G:533 bounds its L² norm by 343 times the cube majorant norm. CutoffGagliardo.lean:511 is exactly the all-offset lattice-count inequality used. Replacing sqrt(343) by 343 at G:548 is a valid loss. G:575 and :625–697 close the norm and constant arithmetic.

6. **Other reported declarations and audit coverage: PASS.** G:184/:188, :252/:257, :280, :386, :399/:409, :439/:444, :460 are the reported generic calculus, support, norm and periodicity results. All 52 top-level theorem/def declarations occur exactly once in research/T12/axioms_u5.lean:10–61; no missing or extra audit entry. Every entry has exactly [propext, Classical.choice, Quot.sound], including Csix and gradientLSix. Line wrapping makes the worker's “52 lines” (REPORT_400.md:82) mean 52 entries; this is not an axiom discrepancy.

7. **Non-vacuity and negative check: PASS.** research/T12/probes/gradient_l6_closes.lean:85, :115, :117, :123, :126 constructs a cosine field, subtracts its mean, proves smooth periodicity, mean zero and nonzeroness, and applies the theorem at :158. That is the required nonzero instance. Reviewer probe rev400_finiteness.lean:15–21 additionally proves the Laplacian norm and full RHS are finite for every smooth periodic v. rev400_negative_constant.lean:10–14 changes Csix to zero while preserving every hypothesis and argument; the exact-field proof fails with the expected coefficient type mismatch. This is a substantive constant mutation, not a dropped argument. It tests rejection by the supplied proof, not a separately formalized counterexample to the mutated assertion.

8. **Hygiene and scope: PASS.** The three-dot diff adds only one Lean module and its research probes/audit, and updates the authorized records. No existing module or verification file is changed. G:40 is the only forbidden-word grep match, inside documentation; there is no forbidden declaration/tactic and no maxHeartbeats override. The module has no warnings on direct elaboration. experiments/build_changed_lean.py:10–23 selects the added formalization module, so it is covered by the changed-module CI build even before API registration.

## 3. Gaps and exact one-line fixes

No mathematical residual or blocking build issue was found. Two documentation findings require only the following one-line corrections, applied by the worker, not by this reviewer:

1. **Minor — support belongs to the localized Laplacian.** G:28–29, research/T12/ATTEMPTS_U5.md:16–17 and research/T12/T12_SPLIT.md:129–130 describe the periodic majorant as supported in the ball. G:428 and :469 define and prove its periodicity; the proof actually uses the indicator at G:478. At each occurrence replace the support wording with: **“The localized Laplacian Δ(χv) is supported in closedBall 0 3; the periodic majorant is multiplied by that ball's indicator.”** For G this can be done by replacing line 29 alone; for ATTEMPTS replace line 16 with “(lap_cutoffMul_eq) → the periodic pointwise majorant, with Δ(χv) supported in”; for T12_SPLIT replace line 130 with “norm_lap_cutoffMul_le; Δ(χv) is supported in tsupport χ = closedBall 0 3 → lattice tiling”.

2. **Minor — overbroad library-absence claim.** research/T12/REPORT_400.md:65 and research/T12/ATTEMPTS_U5.md:86–87 say Mathlib supplies no explicit C⁰/C² bounds for ContDiffBump. The C⁰ part is incorrect: Cutoff.lean:73 already gives 0 ≤ χ ≤ 1, directly from Mathlib/Analysis/Calculus/BumpFunction/Basic.lean:142, :148. Replace the report's absence clause with **“The C⁰ bound 0 ≤ χ ≤ 1 is explicit; numerical first- and second-derivative bounds were not supplied by this lane.”** Replace ATTEMPTS line 86 with **“numeric would require numerical first- and second-derivative bounds, which this lane does”**, retaining line 87 “not provide.” The fixed positive choice-defined constant already satisfies the brief.

The report's other limitation (REPORT_400.md:66) is accurate: the supplied probe does not prove the L⁶ gradient norm is nonzero. This is not required once a genuine nonzero mean-zero witness and finite RHS have been checked. No additional non-vacuity construction is needed.

**Whole Section4 searches before assessing gap claims.** Ran the following grep -rn searches over the entire requested tree:
```text
grep -rnE 'ContDiffBump|cutoff.*(bound|Bound)|bump.*(bound|Bound)' formalization/NSFormalization/Section4
grep -rnE 'bump.*(deriv|bound)|chi_deriv_bound|cutoff.*(deriv|bound)' formalization/NSFormalization/Section4
grep -rnE 'gradient.*(ne_zero|pos)|eLpNorm.*(ne_zero|pos)|reweightDatum|complex.*multiplier' formalization/NSFormalization/Section4
grep -rnE 'probeMZ|periodicLpENorm.*gradientTensor.*(≠|<|>)' formalization/NSFormalization/Section4
```

Relevant hits were opened: Section4/D01/OrderZeroSymbol.lean:47–51 already has bump_nonneg/bump_le1, :89 gives a derivative estimate conditional on a bound, and :114 proves existence of that bound; Section4/B02/Annular.lean:305 has an explicit zeroth-order bound; Section4/D01/HomogeneousWitness.lean:300 only constructs a bump for local integrability. None supplies numerical second-derivative constants for this lane's cutoff. The final search returned no matches (exit 1). The broad gradient search found the known gradientL6Const_pos and unrelated whole-space norm estimates, not positivity for probeMZ. T12 probe searches likewise show the reported witness but no positive-gradient-norm theorem. These searches support the limited observations above, not a claim that no such theorem could exist anywhere in Mathlib. The real-only reweightDatum limitation was independently checked at SpectralGap.lean:127; the report's estimated “~100 lines” for an alternative proof is speculation, not a required residual.

## 4. Commands and results

All Lean commands source . scripts/lean-env.sh at the worktree root, then run lake from verification/ with LEAN_NUM_THREADS=6. Only this new report and the two allowed rev400_*.lean probes were written; no git mutation, source fix or record edit was made.

### Module build

Command: LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.GradientLSix. Exit 0. Exact captured output follows (replayed dependency warnings; no message from GradientLSix itself):
```text
⚠ [8778/9087] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9824/10000] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
warning: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:51: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9825/10000] Replayed NSFormalization.Paper1.PeriodicH2Embedding
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:148:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:263:23: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:268:9: Variable name `k` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _k

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9836/10000] Replayed Formal.EndpointSafeTwoSpacePicard
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:126:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:627:18: `continuousOn_iff_continuous_restrict` has been deprecated: Use `continuousOn_iff_continuous_domRestrict` instead
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:766:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:768:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:839:21: `continuousOn_iff_continuous_restrict` has been deprecated: Use `continuousOn_iff_continuous_domRestrict` instead
⚠ [9838/10000] Replayed NSFormalization.Paper1.PeriodicWeightShift
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: Unused tactic linter: `ring` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
⚠ [9840/10000] Replayed NSFormalization.Paper1.LocalizationBoundary
warning: NSFormalization/Paper1/LocalizationBoundary.lean:355:36: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/LocalizationBoundary.lean:361:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
⚠ [9863/10000] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9867/10000] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9874/10000] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9877/10000] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9887/10000] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9890/10000] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [9904/10000] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9921/10000] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [9966/10000] Replayed NSFormalization.Paper1.PeriodicScalarForceEndpoints
warning: NSFormalization/Paper1/PeriodicScalarForceEndpoints.lean:156:5: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
⚠ [9970/10000] Replayed NSFormalization.Paper1.PeriodicForceConvergence
warning: NSFormalization/Paper1/PeriodicForceConvergence.lean:53:13: This simp argument is unused:
  Pi.neg_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [mul_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9971/10000] Replayed NSFormalization.Paper1.PeriodicInsertionSupport
warning: NSFormalization/Paper1/PeriodicInsertionSupport.lean:129:13: Variable name `hr` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hr

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9973/10000] Replayed NSFormalization.Paper1.PeriodicPacketEndpointRates
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:45:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:72:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9974/10000] Replayed NSFormalization.Paper1.PeriodicCorrectionEndpointRates
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:43:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:44:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:69:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:70:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9982/10000] Replayed NSFormalization.Paper1.PeriodicDensityFiber
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:85:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:118:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9986/10000] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _U

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10000 jobs).
```

### Direct elaboration

Each command below exited 0 with exactly zero output:
```text
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T12/GradientLSix.lean
LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/gradient_l6_closes.lean
LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/rev400_finiteness.lean
```

### Axioms

Command: LEAN_NUM_THREADS=6 lake env lean ../research/T12/axioms_u5.lean. Exit 0. Exact output (52 entries, all exactly the required three axioms):
```text
'NSFormalization.Section3.T12.inverseWeight_abs_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.inverseWeight_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.homogeneousRatio_one_abs_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.homogeneousDatumWeight_one_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.periodicLpENorm_two_le_laplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.periodicHomogeneousENorm_one_le_sobolev_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.periodicLpENorm_gradientTensor_le_laplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.contDiff_dirDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.hasCompactSupport_dirDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.dirDeriv_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.dirDeriv_add_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.dirDeriv_cutoffMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.dirDeriv_two_cutoffMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.lap_cutoffMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.contDiff_lap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.hasCompactSupport_lap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.exists_cutoff_lap_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.smoothL2_cutoffMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.norm_coordinateVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.norm_dirDeriv_le_norm_gradTensor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.cutoffGradBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffGradBound_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffGradBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.norm_dirDeriv_cutoff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffLapBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffLapBound_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffLapBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.leibnizConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.leibnizConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.norm_lap_cutoffMul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.tsupport_cutoff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.support_cutoffMul_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eqOn_zero_dirDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eqOn_zero_lap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.lap_cutoffMul_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.leibnizMajorant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.leibnizMajorant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.norm_gradTensor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.continuous_norm_gradTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.continuous_leibnizMajorant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.isPeriodicSpatial_gradientTensor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.isPeriodicSpatial_leibnizMajorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.enorm_lap_cutoffMul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.measurable_enn_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.lintegral_lap_cutoffMul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_lap_cutoffMul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.gradTensor_cutoffMul_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_leibnizMajorant_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.Csix' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.Csix_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.ofReal_Csix' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.gradientLSix' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Negative mutation

Command: LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/rev400_negative_constant.lean. Exit 1, expected. Exact output:
```text
../research/T12/probes/rev400_negative_constant.lean:14:2: error: Type mismatch
  gradientLSix
has type
  ∀ (v : SpatialField),
    SmoothPeriodicT v →
      IsMeanZeroT v → periodicLpENorm 6 (gradientTensor v) ≤ ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)
but is expected to have type
  ∀ (v : SpatialField),
    SmoothPeriodicT v →
      IsMeanZeroT v → periodicLpENorm 6 (gradientTensor v) ≤ ENNReal.ofReal 0 * periodicLpENorm 2 (laplacian v)
```

### make check

Command: LEAN_NUM_THREADS=6 make check. Exit 0 on both runs. The second run captured stdout/stderr together in memory to recover exact head/tail after the first tool response was truncated. Output is 47,563 lines; following logs/LESSONS.md's review-log guidance, only the first and last 40 lines are pasted verbatim, with the omitted middle explicitly marked. The existing global umbrella report mentions a BoundaryCorollary sorry and source_hashes_match=false; those are not lane-module diagnostics or dependencies in the audited theorem's axiom set.

First 40 lines:
```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 628,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 42,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
```

[47,483 middle lines omitted: source/contract closure JSON.]

Last 40 lines:
```text
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.Localization"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

### Diff, hygiene and conditional gates

Command: git diff --name-only origin/erenup/integration-section3...HEAD. Exit 0, exact output:
```text
formalization/NSFormalization/Section3/T12/GradientLSix.lean
logs/LESSONS.md
research/T12/ATTEMPTS_U5.md
research/T12/REPORT_400.md
research/T12/T12_SPLIT.md
research/T12/axioms_u5.lean
research/T12/probes/gradient_l6_closes.lean
```

git diff --name-status on the same range marks GradientLSix and the four new research files A, and only LESSONS/T12_SPLIT M. git diff --check origin/erenup/integration-section3...HEAD and git diff --check both exit 0 with no output.

Command: rg -n '\\b(sorry|admit|axiom|native_decide|maxHeartbeats)\\b' formalization/NSFormalization/Section3/T12/GradientLSix.lean research/T12/probes/gradient_l6_closes.lean. Exit 0, exact output:
```text
formalization/NSFormalization/Section3/T12/GradientLSix.lean:40:No `sorry`, no `axiom`, no `native_decide`, no named goal input; every declaration
```

git diff --name-only origin/erenup/integration-section3...HEAD -- verification/ exits 0 with zero output. Therefore the user's conditional scripts/gates.sh and check_contracts.py --base-ref origin/erenup/integration-section3 gates do not apply; neither is claimed to have run. make check does run the ordinary check_contracts.py architecture gate, as shown above.

Command: python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration-section3 --dry-run. Exit 0, exact output:
```text
Changed Lean modules: NSFormalization.Section3.T12.GradientLSix, NSFormalization.Section3.T16.Assembly, NSFormalization.Section3.T17.ForceProfile
```

The dry-run script uses a two-dot comparison (experiments/build_changed_lean.py:35–36); its extra T16/T17 names are not changes in this lane's three-dot diff. GradientLSix is selected as required. Initial git status was clean; final added files are this review, rev400_finiteness.lean and the intentionally failing rev400_negative_constant.lean. Existing lane files remain unchanged.

