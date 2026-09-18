ACCEPT-WITH-NOTES

## 1. What the lane claims

Review scope: the **smooth partial result expressly permitted by the brief**, not completion of the general API field. The report states this distinction at research/T12/REPORT_396.md:15 and :35; the status agrees at research/T12/T12_SPLIT.md:112. The unresolved field is research/T12/probes/api_on_canonical.lean:148.

The paper, opened with `sed -n '20,31p' paper/sections/appendix-b-embeddings.tex` (also read :1–38), asks for mean-zero periodic distributions with finite homogeneous norm, and gives the L³ estimate at :29. Smoothness is a genuine restriction, not the paper's full hypothesis. It is disclosed and authorized by the fallback in this lane's brief.

## 2. What is in Lean

All six claimed declarations exist in formalization/NSFormalization/Section3/T12/CriticalL3.lean:

| Line | Declaration / exact mathematical type |
|---|---|
| 61 | `a05_dotHomogeneousENorm_eq : A05.dotHomogeneousENorm = D01.dotHomogeneousENorm` |
| 72 | `periodicSobolevENorm_zero_le_half (v : SpatialField) : periodicSobolevENorm 0 v ≤ periodicSobolevENorm (1 / 2) v` |
| 117 | `l2Q_le_homogeneous_half (v : SpatialField) (hv : SmoothPeriodicT v) (hmem : MemPeriodicHomogeneous (1 / 2) v) : eLpNorm v 2 (volume.restrict fundamentalCube) ≤ ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v` |
| 134 | `CcriticalHalf : ℝ := criticalL3Const * cutoffGagliardoConst * (gapConst (1 / 2) + 1)` |
| 138 | `CcriticalHalf_pos : 0 < CcriticalHalf` |
| 151 | `velocityCriticalL3_smooth (v : SpatialField) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) : periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v` |

The proof is the stated analytic chain, not a named-input repackaging. Verified the cited tree declarations by opening their source:
- Haar/cube equality: Section3/T12/HaarCube.lean:150, :183; cutoff agreement and smooth H∞ membership: Section3/T12/Cutoff.lean:185, :190.
- Registered whole-space estimate and positive constant: Section4/A05/CriticalL3.lean:394, :302, :305. Its H∞ hypothesis is actual smoothness plus Sobolev data at every natural order (Section4/A02/SolutionClass.lean:88).
- Local rfl norm bridge at CriticalL3.lean:61 agrees with verification/Bindings/GradientL6V2.lean:38. The brief's cited :44 is the further bridge to the contract norm, not literally the local D01 bridge; both were read.
- U3 comparison: Section3/T12/CutoffGagliardo.lean:974; its constant at :962. Spectral gap: Section3/T12/SpectralGap.lean:331, with inhomogeneous norm on the LHS. The lane correctly supplies the extra order-monotonicity and Parseval steps rather than misquoting spectralGap as a direct physical L² bound. Parseval is Section3/T15/ParsevalZero.lean:52.
- Membership carries periodicity, physical L², zero mean and finite homogeneous norm, with no smoothness (Section3/T12/MeanZeroCalculus.lean:60). SmoothPeriodicT is the honest conjunction of smoothness and periodicity (:66). No hidden contradictory input, empty interval or unused extra binder was introduced. The main proof's top branch (CriticalL3.lean:154) is valid totalization, not the only possible branch.
- Worker nonzero witness: research/T12/probes/critical_l3_closes.lean:63, :101, :105, :109, :135. Reviewer strengthened it with finite homogeneous norm and actual membership at research/T12/probes/rev396_nonvacuity.lean:144 and :148, using Section3/T13/TorusIdentity.lean:1089. This rules out an infinite-RHS-only demonstration.
- No banned proof token, heartbeat override, or anonymous instance occurs in the new U4 module. The inherited U3 module also has no banned token or heartbeat override. All six U4 axiom audits are exactly the standard three.
- No existing Lean module changed. Triple-dot diff includes the inherited U3 files and one modified planning record, T12_SPLIT.md; this is the specifically requested status update, not a modified module. No verification/ file changed, so the user's conditional scripts/gates.sh and base-aware check_contracts gates do not apply. Changed formalization modules are covered by experiments/build_changed_lean.py:18–20, :32–37.

## 3. Gaps and exact one-line fixes

1. **Documentation correction:** research/T12/ATTEMPTS_U4.md:83–85 incorrectly says none of the four ingredients is in Mathlib for the unit torus. Replace that sentence with: “Mathlib's MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm supplies lower semicontinuity for arbitrary measures, including torus Haar; the remaining work is the smooth periodic mean-zero approximation, its homogeneous norm control, and convergence.”
2. **Matching report correction:** research/T12/REPORT_396.md:40, replace “The L³ lower semicontinuity of the LHS (whose finiteness is the conclusion) is the crux — a separate L lane.” with: “Lower semicontinuity is available as MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm; the remaining density lane must construct approximants with the required homogeneous norm bound and convergence.”

Evidence: verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean:73–76 quantifies over arbitrary μ and p and requires a.e. convergence plus AEStronglyMeasurable approximants, **no finite L³ norm for the limit**. Its statement was opened with sed.

Whole Section4 searches required by this review:
```sh
grep -rnEi 'mollif|approximate.?identity|eLpNorm.*liminf|liminf.*eLpNorm|periodic.*dens|dens.*periodic' formalization/NSFormalization/Section4
grep -rnEi 'periodicHomogeneous|torus.*(approxim|converg)|smooth.*dens|dens.*smooth' formalization/NSFormalization/Section4
grep -rnEi 'periodicHomogeneousENorm|periodic.*mollif|mollif.*periodic|eLpNorm_lim_le_liminf' formalization/NSFormalization/Section4
```
The last search is empty (exit 1). Broader searches find B02/Annular.lean:338 (whole-space annular smoothing), B02/AnnularReal.lean:218 (whole-space homogeneous density), D01/HomogeneousWitness.lean:517 (compact whole-space datum existence), and A01/CoordinateTame.lean:150 (integer-order cylinder estimate by density). These were opened and do not supply the required canonical periodic half-order approximation/contraction/convergence package. Thus the periodic residual is credible; a blanket claim of absent lower semicontinuity is not.

The main residual remains exactly:
```lean
theorem velocityCriticalL3 (v : SpatialField)
    (hv : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v ≤
      ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v
```
This review does not certify U6 assembly or claim the above general theorem has been proved.

## 4. Commands and results

All lake commands ran after `. scripts/lean-env.sh`, from verification/, with LEAN_NUM_THREADS=6, one lake process at a time. No installation was needed; the existing environment successfully compiled all requested targets. No git state changes or worker-file edits were made.

### Build (exit 0)

`LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.CriticalL3`

Exact output below. All replayed diagnostics belong to dependencies; the reviewed module emits no diagnostics.
```text
⚠ [8778/8863] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9047/9083] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9051/9083] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9058/9083] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9061/9083] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9071/9083] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9341/9357] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [9869/9934] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9900/9934] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [9914/9934] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
warning: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:51: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9915/9934] Replayed NSFormalization.Paper1.PeriodicH2Embedding
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
⚠ [9951/10019] Replayed NSFormalization.Paper1.LocalizationBoundary
warning: NSFormalization/Paper1/LocalizationBoundary.lean:355:36: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/LocalizationBoundary.lean:361:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
⚠ [9953/10019] Replayed NSFormalization.Paper1.PeriodicScalarForceEndpoints
warning: NSFormalization/Paper1/PeriodicScalarForceEndpoints.lean:156:5: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
⚠ [9958/10019] Replayed NSFormalization.Paper1.PeriodicForceConvergence
warning: NSFormalization/Paper1/PeriodicForceConvergence.lean:53:13: This simp argument is unused:
  Pi.neg_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [mul_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9960/10019] Replayed NSFormalization.Paper1.PeriodicInsertionSupport
warning: NSFormalization/Paper1/PeriodicInsertionSupport.lean:129:13: Variable name `hr` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hr

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9962/10019] Replayed NSFormalization.Paper1.PeriodicPacketEndpointRates
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:45:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:72:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9963/10019] Replayed NSFormalization.Paper1.PeriodicCorrectionEndpointRates
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:43:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:44:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:69:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:70:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9971/10019] Replayed NSFormalization.Paper1.PeriodicDensityFiber
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:85:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:118:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9975/10019] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
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
⚠ [9983/10019] Replayed Formal.EndpointSafeTwoSpacePicard
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
⚠ [9988/10019] Replayed NSFormalization.Paper1.PeriodicWeightShift
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: Unused tactic linter: `ring` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
⚠ [10018/10039] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hB

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:49:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10030/10039] Replayed NSFormalization.Source.RieszFourierScale
info: NSFormalization/Source/RieszFourierScale.lean:70:57: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10036/10039] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10037/10039] Replayed NSFormalization.Source.FractionalRealization
warning: NSFormalization/Source/FractionalRealization.lean:60:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
Build completed successfully (10039 jobs).
```

### Direct checks

```text
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T12/CriticalL3.lean
[0 output; exit 0]
LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/critical_l3_closes.lean
[0 output; exit 0]
LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/rev396_nonvacuity.lean
[0 output; exit 0]
```

`LEAN_NUM_THREADS=6 lake env lean ../research/T12/axioms_u4.lean` (exit 0), exact output:
```text
'NSFormalization.Section3.T12.a05_dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.periodicSobolevENorm_zero_le_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.l2Q_le_homogeneous_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.CcriticalHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.CcriticalHalf_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.velocityCriticalL3_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Substantive negative mutation

research/T12/probes/rev396_mutation.lean:16 copies the entire main proof, retaining every argument, and changes only the claimed bound's constant from CcriticalHalf to 0 (:18). This is a stronger mathematical claim, not an omitted-argument test.

`LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/rev396_mutation.lean` exits 1, exact output:
```text
../research/T12/probes/rev396_mutation.lean:21:57: error: Type mismatch
  CcriticalHalf_pos
has type
  0 < CcriticalHalf
but is expected to have type
  0 < 0
../research/T12/probes/rev396_mutation.lean:23:2: error: unsolved goals
case neg.calc.step
v : SpatialField
hv : SmoothPeriodicT v
hmean : IsMeanZeroT v
hfin : ¬periodicHomogeneousENorm (1 / 2) v = ∞
hmem : MemPeriodicHomogeneous (1 / 2) v
hL :
  eLpNorm v 2 (volume.restrict fundamentalCube) ≤ ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v
halg :
  ENNReal.ofReal criticalL3Const *
      (ENNReal.ofReal cutoffGagliardoConst *
        (ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v + periodicHomogeneousENorm (1 / 2) v)) =
    ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v
⊢ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v ≤
    ENNReal.ofReal 0 * periodicHomogeneousENorm (1 / 2) v
```

### make check (exit 0)

Exact head/tail excerpt (huge middle JSON omitted, consistent with logs/LESSONS.md's review-output guidance):
```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 619,
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
[... middle output omitted ...]
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
Ran 13 tests in 0.344s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
EXIT: 0
```
The global architecture output's pre-existing BoundaryCorollary admission is not in the audited module's dependency axioms; the six exact audits above independently confirm this module.

### Hygiene / diff

`rg -n 'sorry|admit|\baxiom\b|native_decide|maxHeartbeats|^instance' formalization/NSFormalization/Section3/T12/CriticalL3.lean`: no output (exit 1 = no matches).

`git diff --name-only origin/erenup/integration-section3...HEAD`, exact output:
```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 6598581d051c41b6068c6bef2d8af238bc3ecb05
formalization/NSFormalization/Section3/T12/CriticalL3.lean
formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean
research/T12/ATTEMPTS_U3.md
research/T12/ATTEMPTS_U4.md
research/T12/REPORT_377.md
research/T12/REPORT_396.md
research/T12/T12_SPLIT.md
research/T12/axioms_u3.lean
research/T12/axioms_u4.lean
research/T12/probes/critical_l3_closes.lean
research/T12/probes/cutoff_gagliardo_closes.lean
```
Companion `git diff --name-status` reports A for every file above except M for research/T12/T12_SPLIT.md. The initial worktree was clean. Reviewer-created artifacts are only this report and rev396_mutation.lean / rev396_nonvacuity.lean.

