# U13 attempts

Route decision: neither (i) nor (ii) can prove the unchanged statement.
`CorrectionAPI.reference_periodic : IsPeriodicOn univ v` is an independent,
global obligation. Agreement in the correction window cannot transfer it.
The counterexample is zero at nonnegative times and the spatial identity at
negative times. It is smooth and periodic on every classical slab, and
has zero divergence at every positive time, but fails periodicity at t = -1.

First compilation of the counterexample used `contDiffOn_const.congr` without
specifying the constant. Exact error:
```
../formalization/NSFormalization/Section3/T17/SlabBridge.lean:37:79: error: unsolved goals
S : ℝ
z : SpaceTime
hz : z ∈ Ico 0 S ×ˢ univ
⊢ 0 = ?m.29

S : ℝ
⊢ Space
```
Fixed by specifying `(c := (0 : Space))`.

Exact residual field: `IsPeriodicOn univ v`, i.e.
`∀ t ∈ univ, ∀ x : Space, ∀ i : Fin 3,
v (t, x + coordinateVector i) = v (t, x)`.
The missing implication from slab periodicity and slab smoothness is false,
not an unproved analytic lemma. `not_correctionStatementSlab` proves this
for the complete requested quantifier block, including all geometry premises.
A T17 V2 with slab-relative reference periodicity, or a conclusion about an
extended reference instead of the original velocity, is required. This
counterexample does not show that T16 needs a V2.

Repository discrepancy: `grep -rn 'G5' research/T17` returned no matches;
the supplied G5 discussion is in the lane brief but not SPEC_ISSUES.md.
The canonical `localPotentialAPI` theorem is in T16/Assembly.lean, not
T16/LocalPotential.lean. No existing file is edited; the split status is
recorded in the new T17_SPLIT_U13.md to respect the new-files-only rule.

## Continuation: cutoff extension

First elaboration, missing evaluation point in `Differentiable.differentiableAt`:
```text
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:67:15: error: don't know how to synthesize implicit argument `x`
  @Differentiable.differentiableAt ℝ DenselyNormedField.toNontriviallyNormedField Space
    (PiLp.normedAddCommGroup 2 fun x => ℝ).toAddCommGroup (PiLp.normedSpace 2 ℝ fun x => ℝ).toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace Space (PiLp.normedAddCommGroup 2 fun x => ℝ).toAddCommGroup
    (PiLp.normedSpace 2 ℝ fun x => ℝ).toModule PseudoMetricSpace.toUniformSpace.toTopologicalSpace (fun y => v (t, y))
    ?m.603
    (ContDiff.differentiable hvs
      (of_eq_true
        (Eq.trans (congrArg Not (Eq.trans WithTop.coe_eq_zero._simp_1 ENat.top_ne_zero._simp_1)) not_false_eq_true)))
context:
v : SpaceTimeField
T δ r : ℝ
x₀ : Space
hT : 0 < T
hδ : 0 < δ
hper : IsPeriodicOn univ v
hv : ContDiffOn ℝ ∞ v (Ioo 0 (T + δ) ×ˢ univ)
hdiv : ∀ t ∈ Ioo 0 (T + δ), ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0
m : ℝ := ⋯
hm : 0 < m
χ : ContDiffBump T := ⋯
V : SpaceTimeField := ⋯
hc : ContDiff ℝ ∞ fun z => ↑χ z.1
hs : (tsupport fun z => ↑χ z.1) ⊆ Ioo 0 (T + δ) ×ˢ univ
t : ℝ
ht : t ∈ Ioo 0 (T + δ)
x : Space
hx : x ∈ ball x₀ r
hvs : ContDiff ℝ ∞ fun y => v (t, y)
⊢ Space
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:67:9: error: failed to infer `have` declaration type
```
Fixed by evaluating `hvs.differentiable` at `x`.

Second elaboration (Pi operations versus lambda forms):
```text
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:69:6: warning: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:70:4: error: 'change' tactic failed, pattern
  ↑χ t * spatialDivergence v t x = 0
is not definitionally equal to target
  ∑ i, ((fderiv ℝ (fun y => ↑χ t • v (t, y)) x) (coordinateVector i)).ofLp i = 0
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:68:56: warning: This simp argument is unused:
  fderiv_const_smul hd

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialDivergence, spatialDerivative, V, ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul, ← Finset.mul_sum]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:69:6: warning: This simp argument is unused:
  ContinuousLinearMap.smul_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialDivergence, spatialDerivative, V, fderiv_const_smul hd, PiLp.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:69:38: warning: This simp argument is unused:
  PiLp.smul_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialDivergence, spatialDerivative, V, fderiv_const_smul hd, ContinuousLinearMap.smul_apply,
    smul_eq_mul, ← Finset.mul_sum]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:69:55: warning: This simp argument is unused:
  smul_eq_mul

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialDivergence, spatialDerivative, V, fderiv_const_smul hd, ContinuousLinearMap.smul_apply,
    PiLp.smul_apply, ← Finset.mul_sum]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:69:68: warning: This simp argument is unused:
  ← Finset.mul_sum

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialDivergence, spatialDerivative, V, fderiv_const_smul hd, ContinuousLinearMap.smul_apply,
    PiLp.smul_apply, smul_eq_mul]

Note: Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning.

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:129:64: error: unsolved goals
v V : SpaceTimeField
D E : CutoffData
ε ν : ℝ
I : Set ℝ
hw : D.correction ε = E.correction ε
hs : tsupport (D.correction ε) ⊆ I ×ˢ univ
heq : ∀ t ∈ I, ∀ (x : Space), v (t, x) = V (t, x)
z : SpaceTime
ht : z.1 ∉ I
hz : ∀ (x : Space), D.correction ε (z.1, x) = 0
⊢ fderiv ℝ (fun x => 0) z.2 = 0
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:131:46: warning: `ContinuousLinearMap.zero_apply` has been deprecated: Use `zero_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.zero_apply` to `zero_apply x`).
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:124:57: warning: This simp argument is unused:
  hv

Hint: Omit it from the simp argument list.
  [apply] simp only [correctionForce, ← hw, spatialDerivative, heq z.1 ht]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:130:47: warning: This simp argument is unused:
  fderiv_const

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialDerivative, funext hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

Assembly elaboration: the simplifier did not unfold the concrete cutoff records to identify their cylinders/radii:
```text
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:260:6: error: Type mismatch: After simplification, term
  A.correction_profile_smooth ε hε
 has type
  @ContDiffOn ℝ DenselyNormedField.toNontriviallyNormedField SpaceTime Prod.normedAddCommGroup Prod.normedSpace Space
    (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ) ∞
    (rescaledCorrectionProfile V place.x₀ place.T ε E) (fixedProfileCylinder E)
but is expected to have type
  @ContDiffOn ℝ DenselyNormedField.toNontriviallyNormedField SpaceTime Prod.normedAddCommGroup Prod.normedSpace Space
    (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ) ∞
    (rescaledCorrectionProfile V place.x₀ place.T ε E) (fixedProfileCylinder D)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:263:6: error: Type mismatch: After simplification, term
  A.correction_profile_support ε hε
 has type
  @LE.le (Set SpaceTime) instLE (tsupport (rescaledCorrectionProfile V place.x₀ place.T ε E)) (fixedProfileCylinder E)
but is expected to have type
  @LE.le (Set SpaceTime) instLE (tsupport (rescaledCorrectionProfile V place.x₀ place.T ε E)) (fixedProfileCylinder D)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:268:6: error: Type mismatch: After simplification, term
  A.correction_profile_uniform k ε hε
 has type
  ∀ z ∈ fixedProfileCylinder E,
    @LE.le ℝ Real.instLE ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile V place.x₀ place.T ε E) z‖
      (A.correctionProfileConst k)
but is expected to have type
  ∀ z ∈ fixedProfileCylinder D,
    @LE.le ℝ Real.instLE ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile V place.x₀ place.T ε E) z‖
      (A.correctionProfileConst k)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:271:6: error: Type mismatch: After simplification, term
  A.force_profile_smooth ε hε
 has type
  @ContDiffOn ℝ DenselyNormedField.toNontriviallyNormedField SpaceTime Prod.normedAddCommGroup Prod.normedSpace Space
    (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ) ∞
    (rescaledForceProfile ν V place.x₀ place.T ε E) (fixedProfileCylinder E)
but is expected to have type
  @ContDiffOn ℝ DenselyNormedField.toNontriviallyNormedField SpaceTime Prod.normedAddCommGroup Prod.normedSpace Space
    (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ) ∞
    (rescaledForceProfile ν V place.x₀ place.T ε E) (fixedProfileCylinder D)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:274:6: error: Type mismatch: After simplification, term
  A.force_profile_support ε hε
 has type
  @LE.le (Set SpaceTime) instLE (tsupport (rescaledForceProfile ν V place.x₀ place.T ε E)) (fixedProfileCylinder E)
but is expected to have type
  @LE.le (Set SpaceTime) instLE (tsupport (rescaledForceProfile ν V place.x₀ place.T ε E)) (fixedProfileCylinder D)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:279:6: error: Type mismatch: After simplification, term
  A.force_profile_uniform k ε hε
 has type
  ∀ z ∈ fixedProfileCylinder E,
    @LE.le ℝ Real.instLE ‖iteratedFDeriv ℝ k (rescaledForceProfile ν V place.x₀ place.T ε E) z‖ (A.forceProfileConst k)
but is expected to have type
  ∀ z ∈ fixedProfileCylinder D,
    @LE.le ℝ Real.instLE ‖iteratedFDeriv ℝ k (rescaledForceProfile ν V place.x₀ place.T ε E) z‖ (A.forceProfileConst k)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:282:6: error: Type mismatch: After simplification, term
  A.correction_profile_identity ε hε
 has type
  ∀ z ∈ fixedProfileCylinder E,
    @Eq Space (E.correction ε (correctionChartPoint place.x₀ place.T ε z))
      (rescaledCorrectionProfile V place.x₀ place.T ε E z)
but is expected to have type
  ∀ z ∈ fixedProfileCylinder D,
    @Eq Space (E.correction ε (correctionChartPoint place.x₀ place.T ε z))
      (rescaledCorrectionProfile V place.x₀ place.T ε E z)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:285:6: error: Type mismatch: After simplification, term
  A.force_profile_identity ε hε
 has type
  ∀ z ∈ fixedProfileCylinder E,
    @Eq Space (correctionForce ν V E ε (correctionChartPoint place.x₀ place.T ε z))
      ((ε ^ 2)⁻¹ • rescaledForceProfile ν V place.x₀ place.T ε E z)
but is expected to have type
  ∀ z ∈ fixedProfileCylinder D,
    @Eq Space (correctionForce ν V E ε (correctionChartPoint place.x₀ place.T ε z))
      ((ε ^ 2)⁻¹ • rescaledForceProfile ν V place.x₀ place.T ε E z)
../formalization/NSFormalization/Section3/T17/SlabBridge2.lean:294:6: error: Type mismatch: After simplification, term
  A.force_support ε hε
 has type
  @LE.le (Set SpaceTime) instLE (tsupport (correctionForce ν V E ε))
    (Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ periodicSet (ball place.x₀ (ε * E.θRadius)))
but is expected to have type
  @LE.le (Set SpaceTime) instLE (tsupport (correctionForce ν V E ε))
    (Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ periodicSet (ball place.x₀ (ε * D.θRadius)))
```
Fixed by explicit `rfl` cylinder/radius equalities. The cutoff, physical correction, force, and profile locality lemmas all elaborated without further errors.

## Continuation outcome: proved, no residual

The second statement keeps `IsPeriodicOn univ v` and uses open-slab
`ContDiffOn`. `SlabBridge2.correctionStatementSlab'_holds` (in the T17
namespace) proves the exact block. No T16 generalization is necessary:
`T16.Assembly.localPotentialAPI` already consumes cylinder `ContDiffOn`.

The proposed scale inference needed repair: `2ε² < m` does not imply
`2ε² ≤ m/2`. The proof calls `exists_threshold` at `T/2, δ/2`, then takes
`min ε₁ place.ε₀`. This gives `2ε² < min T δ / 2`. A `ContDiffBump T` with
inner radius `m/2` and outer radius `3m/4` supplies the extension. T16's
`contDiff_cutoffSmul_of_ballSmooth` handles the global gluing.

The successful locality lemmas give global physical-correction, correction-
profile, correction-force, and force-profile equalities. Outside the window,
the correction is zero on the entire spatial slice, so its spatial derivative
is zero and both reference-dependent force terms vanish. Inside it, the
reference slices and their spatial derivatives coincide. The rescaled-reference
lemma separately records equality on the fixed cylinder. No equality of the
full cutoff records or of their unrestricted potentials is asserted.

The first classical probe elaborated with only deprecated `if_pos`/`if_neg`
warnings (no proof errors); replacing them with `ite_eq_left`/`ite_eq_right`
makes it silent. The final axiom audit includes the theorem whose identifier
contains an interior apostrophe (`correctionStatementSlab'_holds`), and guarded
audits of all five named classical-probe declarations.

The supplied G5 addendum is still absent from this checkout's
`SPEC_ISSUES.md`; the continuation prompt supplies the authoritative ruling.
Existing canonical modules/contracts/bindings/tests are untouched; only the
explicitly requested U13 research records are updated. Full field audit and
gates: `REPORT_460b.md`.
