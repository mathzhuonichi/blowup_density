import NSFormalization.Section3.T20.CriticalTrilinear
import NSFormalization.Section3.T20.MeanReduction
import NSFormalization.Section3.T13.TorusIdentity

/-!
# T20 unit U8 — the critical energy inequality (`eq:criticalenergy`, `03-torus.tex:420-440`)

For the zero initial datum and a force `g ∈ F_T`, the mean-free velocity
`v = u - m(t)` of a classical torus solution satisfies, at every interior time,

`½(y²)' + (ν - C₀ y) z² ≤ b y`,  `y = ‖v‖_{Ḣ^{1/2}}`, `z = ‖v‖_{Ḣ^{3/2}}`,
`b = ‖h‖_{Ḣ^{1/2}}`, `C₀ = criticalTrilinearConst`,

with an actual derivative witness for `(y²)'`.  This is the `criticalEnergy`
field of `CriticalRegularityTAPI` verbatim.

## Route

* §1 Torus Parseval for the real `L²(T³)` pairing of two smooth periodic vector
  fields (Mathlib's `UnitAddTorus.hasSum_prod_mFourierCoeff` per component).
* §2 The constant transport `(m·∇)` acts on the `k`-th coefficient by the purely
  imaginary symbol `∑ⱼ mⱼ·2πikⱼ`, so it contributes nothing to the pairing at
  any frequency (`03-torus.tex:411`, the skew-adjointness step, done on the
  Fourier side).
* §3 The order-`1/2` homogeneous frequency energy `critFreqEnergy` and its
  termwise time derivative, differentiated under the sum exactly as T11's
  `hasDerivAt_torusSobolevNormAt_sq` does at integer order.  The homogeneous
  weight `homogeneousDatumWeight (1/2) k ^ 2 = 2π|k|` is dominated by T11's
  order-`1` inhomogeneous weight, which is what makes the T11 majorant apply.
* §4 `y(r)² = ∑ₖ critFreqEnergy u k r` and `z(t)² = ∑ₖ |2πk|³ …`, through
  `T13.exists_homogeneous_datum` and the mean-reduction slice identity
  `v(r,·) = meanZeroPartT (u(r,·))` (lane 389's `mean_formula`).
* §5 The frequency split of the differentiated energy: the pressure term drops by
  coefficient-side solenoidality (T11's `freqEnergyDerivT_split` at order `0`).
* §6 Assembly: dissipation `-2ν z²`, force `+2⟪Λ^{1/2}h, Λ^{1/2}v⟫ ≤ 2 b y`
  (Cauchy–Schwarz on the coefficient side, `T11.torusRealPairing_le`), convection
  `-2⟪(v·∇)v, Λv⟫` bounded by lane 413's `criticalTrilinear_pairing`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
override, no named goal input.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators ComplexConjugate

/-! ## §1  Torus Parseval for the real `L²` pairing -/

private theorem continuous_component_ofReal {z : SpatialField} (hz : Continuous z) (i : Fin 3) :
    Continuous (fun x : Space ↦ ((z x i : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp hz)

private theorem memLp_torusLift_realScalar {f : Space → ℝ} (hf : Continuous f) (q : ℝ≥0∞) :
    MemLp (torusLift f) q periodicTorusMeasure := by
  have hc : MemLp (torusLift (fun x ↦ ((f x : ℝ) : ℂ))) q periodicTorusMeasure :=
    NSFormalization.Paper1.memLp_torusLift (Complex.continuous_ofReal.comp hf) q
  refine hc.of_le ?_ (Filter.Eventually.of_forall fun y ↦ ?_)
  · exact Complex.continuous_re.comp_aestronglyMeasurable hc.aestronglyMeasurable
  · show ‖torusLift f y‖ ≤ ‖((torusLift f y : ℝ) : ℂ)‖
    rw [Complex.norm_real]

private theorem mFourierCoeff_toLp_eq (f : Space → ℂ)
    (hf : MemLp (torusLift f) 2 periodicTorusMeasure) (k : PeriodicFrequency) :
    UnitAddTorus.mFourierCoeff (hf.toLp (torusLift f)) k = periodicFourierCoeff f k := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact fourier_repr_toLp f hf k

private theorem hasSum_scalarPair (f g : Space → ℂ)
    (hf : MemLp (torusLift f) 2 periodicTorusMeasure)
    (hg : MemLp (torusLift g) 2 periodicTorusMeasure) :
    HasSum (fun k : PeriodicFrequency ↦
        conj (periodicFourierCoeff f k) * periodicFourierCoeff g k)
      (∫ y : PeriodicTorus, conj (torusLift f y) * torusLift g y ∂periodicTorusMeasure) := by
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (hf.toLp (torusLift f)) (hg.toLp (torusLift g))
  have hfun : (fun k : PeriodicFrequency ↦
      conj (UnitAddTorus.mFourierCoeff (hf.toLp (torusLift f)) k) *
        UnitAddTorus.mFourierCoeff (hg.toLp (torusLift g)) k) =
      fun k : PeriodicFrequency ↦ conj (periodicFourierCoeff f k) * periodicFourierCoeff g k :=
    funext fun k ↦ by rw [mFourierCoeff_toLp_eq f hf k, mFourierCoeff_toLp_eq g hg k]
  have hint : (∫ y : PeriodicTorus,
        conj ((hf.toLp (torusLift f)) y) * ((hg.toLp (torusLift g)) y) ∂periodicTorusMeasure) =
      ∫ y : PeriodicTorus, conj (torusLift f y) * torusLift g y ∂periodicTorusMeasure := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y hy hy'
    rw [hy, hy']
  rw [hfun, hint] at h
  exact h

private theorem hasSum_vectorPair {z₁ z₂ : SpatialField}
    (h₁ : Continuous z₁) (h₂ : Continuous z₂) :
    HasSum (fun k : PeriodicFrequency ↦
        ∑ i : Fin 3,
          conj (periodicFourierCoeff (fun x ↦ ((z₁ x i : ℝ) : ℂ)) k) *
            periodicFourierCoeff (fun x ↦ ((z₂ x i : ℝ) : ℂ)) k)
      (∑ i : Fin 3, ∫ y : PeriodicTorus,
        conj (torusLift (fun x ↦ ((z₁ x i : ℝ) : ℂ)) y) *
          torusLift (fun x ↦ ((z₂ x i : ℝ) : ℂ)) y ∂periodicTorusMeasure) :=
  hasSum_sum fun i _ ↦ hasSum_scalarPair _ _
    (NSFormalization.Paper1.memLp_torusLift (continuous_component_ofReal h₁ i) 2)
    (NSFormalization.Paper1.memLp_torusLift (continuous_component_ofReal h₂ i) 2)

private theorem re_sum_integral_eq_periodicPairing {z₁ z₂ : SpatialField}
    (h₁ : Continuous z₁) (h₂ : Continuous z₂) :
    (∑ i : Fin 3, ∫ y : PeriodicTorus,
        conj (torusLift (fun x ↦ ((z₁ x i : ℝ) : ℂ)) y) *
          torusLift (fun x ↦ ((z₂ x i : ℝ) : ℂ)) y ∂periodicTorusMeasure).re =
      periodicPairing z₁ z₂ := by
  have key : ∀ i : Fin 3,
      (∫ y : PeriodicTorus,
          conj (torusLift (fun x ↦ ((z₁ x i : ℝ) : ℂ)) y) *
            torusLift (fun x ↦ ((z₂ x i : ℝ) : ℂ)) y ∂periodicTorusMeasure) =
        ((∫ y : PeriodicTorus, torusLift (fun x ↦ z₁ x i * z₂ x i) y ∂periodicTorusMeasure : ℝ) :
          ℂ) := by
    intro i
    have hpt : (fun y : PeriodicTorus ↦
        conj (torusLift (fun x ↦ ((z₁ x i : ℝ) : ℂ)) y) *
          torusLift (fun x ↦ ((z₂ x i : ℝ) : ℂ)) y) =
        fun y : PeriodicTorus ↦
          ((torusLift (fun x ↦ z₁ x i * z₂ x i) y : ℝ) : ℂ) := by
      funext y
      show conj ((torusLift z₁ y i : ℝ) : ℂ) * ((torusLift z₂ y i : ℝ) : ℂ) =
        ((torusLift z₁ y i * torusLift z₂ y i : ℝ) : ℂ)
      rw [Complex.conj_ofReal, Complex.ofReal_mul]
    rw [hpt, integral_complex_ofReal]
  simp only [key]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, ← integral_finsetSum]
  · show _ = ∫ y : PeriodicTorus,
      (inner ℝ (torusLift z₁ y) (torusLift z₂ y) : ℝ) ∂periodicTorusMeasure
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun y ↦ ?_
    show (∑ i : Fin 3, torusLift z₁ y i * torusLift z₂ y i) =
      (inner ℝ (torusLift z₁ y) (torusLift z₂ y) : ℝ)
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by
      simp [RCLike.inner_apply, mul_comm]
  · intro i _
    exact (memLp_torusLift_realScalar
      (((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp h₁).mul
        ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp h₂)) 1).integrable le_rfl

/-- **Torus Parseval for the real `L²(T³)` pairing.**  For two smooth periodic
vector fields the frequency-wise real pairings of the Fourier coefficients sum to
the physical Haar pairing `periodicPairing`. -/
theorem hasSum_periodicPairing {z₁ z₂ : SpatialField}
    (h₁ : SmoothPeriodicT z₁) (h₂ : SmoothPeriodicT z₂) :
    HasSum (fun k : PeriodicFrequency ↦
        (∑ i : Fin 3,
          conj (periodicFourierCoeff (fun x ↦ ((z₁ x i : ℝ) : ℂ)) k) *
            periodicFourierCoeff (fun x ↦ ((z₂ x i : ℝ) : ℂ)) k).re)
      (periodicPairing z₁ z₂) := by
  have hc₁ : Continuous z₁ := h₁.1.continuous
  have hc₂ : Continuous z₂ := h₂.1.continuous
  have hre : HasSum (fun k : PeriodicFrequency ↦
      (∑ i : Fin 3,
        conj (periodicFourierCoeff (fun x ↦ ((z₁ x i : ℝ) : ℂ)) k) *
          periodicFourierCoeff (fun x ↦ ((z₂ x i : ℝ) : ℂ)) k).re)
      ((∑ i : Fin 3, ∫ y : PeriodicTorus,
        conj (torusLift (fun x ↦ ((z₁ x i : ℝ) : ℂ)) y) *
          torusLift (fun x ↦ ((z₂ x i : ℝ) : ℂ)) y ∂periodicTorusMeasure).re) :=
    (hasSum_vectorPair hc₁ hc₂).map Complex.reCLM.toLinearMap.toAddMonoidHom
      Complex.reCLM.continuous
  rwa [re_sum_integral_eq_periodicPairing hc₁ hc₂] at hre

/-! ## §2  The constant transport drops at every frequency (`03-torus.tex:411`) -/

private theorem ofReal_fderiv_dir_component (z : SpatialField) (c : Space) (i : Fin 3)
    (x : Space) :
    (((fderiv ℝ z x c : Space) i : ℝ) : ℂ) =
      ∑ j : Fin 3, ((c j : ℝ) : ℂ) *
        (((fderiv ℝ z x (coordinateVector j) : Space) i : ℝ) : ℂ) := by
  have h0 : (fderiv ℝ z x) c = ∑ j : Fin 3, c j • (fderiv ℝ z x) (coordinateVector j) := by
    conv_lhs => rw [← NavierStokes.PeriodicUniqueness.sum_coordinates c]
    simp only [map_sum, map_smul]
  have h1 : ((fderiv ℝ z x c : Space) i : ℝ) =
      ∑ j : Fin 3, c j * ((fderiv ℝ z x (coordinateVector j) : Space) i) := by
    have e : ∀ w : Space, (w i : ℝ) = EuclideanSpace.proj (𝕜 := ℝ) i w := fun _ ↦ rfl
    rw [e, h0, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul]; rfl
  rw [h1]
  push_cast
  rfl

/-- `03-torus.tex:411`: the spatially constant transport `(c·∇)` acts on the
`k`-th Fourier coefficient through the scalar symbol `∑ⱼ cⱼ·2πikⱼ`. -/
theorem periodicFourierCoeff_fderiv_dir {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) (c : Space) (i : Fin 3)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ (((fderiv ℝ z x c : Space) i : ℝ) : ℂ)) k =
      (∑ j : Fin 3, ((c j : ℝ) : ℂ) * periodicDerivativeSymbol j k) *
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k := by
  have hs1 : ContDiff ℝ 1 z := hs.of_le (by simp)
  have hcont : ∀ j : Fin 3, Continuous (fun x ↦ ((c j : ℝ) : ℂ) *
      (((fderiv ℝ z x (coordinateVector j) : Space) i : ℝ) : ℂ)) := fun j ↦
    continuous_const.mul (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
        (NavierStokes.PeriodicIntegration.continuous_partial hs1 j)))
  have hcoeff : ∀ j : Fin 3,
      periodicFourierCoeff
        (fun x ↦ (((fderiv ℝ z x (coordinateVector j) : Space) i : ℝ) : ℂ)) k =
        periodicDerivativeSymbol j k * periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k :=
    fun j ↦ periodicFourierCoeff_gradientTensor hp hs1 i j k
  have hrw : (fun x ↦ (((fderiv ℝ z x c : Space) i : ℝ) : ℂ)) =
      fun x ↦ ∑ j : Fin 3, ((c j : ℝ) : ℂ) *
        (((fderiv ℝ z x (coordinateVector j) : Space) i : ℝ) : ℂ) :=
    funext fun x ↦ ofReal_fderiv_dir_component z c i x
  rw [hrw, periodicFourierCoeff_finsetSum _ _ (fun j _ ↦ hcont j), Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [periodicFourierCoeff_const_mul, hcoeff j]
  ring

/-- `03-torus.tex:411`: the constant transport contributes nothing to the
critical energy pairing at any single frequency — the Fourier-side form of its
`L²` skew-adjointness. -/
theorem re_sum_conj_fderiv_dir_zero {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) (c : Space) (k : PeriodicFrequency) :
    (∑ i : Fin 3,
      conj (periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k) *
        periodicFourierCoeff (fun x ↦ (((fderiv ℝ z x c : Space) i : ℝ) : ℂ)) k).re = 0 := by
  have hterm : ∀ i : Fin 3,
      conj (periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k) *
          periodicFourierCoeff (fun x ↦ (((fderiv ℝ z x c : Space) i : ℝ) : ℂ)) k =
        (∑ j : Fin 3, ((c j : ℝ) : ℂ) * periodicDerivativeSymbol j k) *
          (conj (periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k) *
            periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k) := by
    intro i
    rw [periodicFourierCoeff_fderiv_dir hs hp c i k]
    ring
  have hSre : (∑ j : Fin 3, ((c j : ℝ) : ℂ) * periodicDerivativeSymbol j k).re = 0 := by
    rw [Complex.re_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp only [periodicDerivativeSymbol, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hTim : (∑ i : Fin 3, conj (periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k) *
      periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k).im = 0 := by
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hterm i), ← Finset.mul_sum, Complex.mul_re, hSre, hTim]
  ring

/-! ## §3  The critical frequency energy and its time derivative -/

/-- The order-`1/2` homogeneous energy of one frequency of a velocity slice. -/
def critFreqEnergy (u : SpaceTimeField) (k : PeriodicFrequency) (r : ℝ) : ℝ :=
  homogeneousDatumWeight (1 / 2) k ^ 2 * ∑ i : Fin 3, ‖velocityCoeffT u i k r‖ ^ 2

/-- The time derivative of `critFreqEnergy`. -/
def critFreqEnergyDeriv (u : SpaceTimeField) (k : PeriodicFrequency) (r : ℝ) : ℝ :=
  homogeneousDatumWeight (1 / 2) k ^ 2 *
    ∑ i : Fin 3, 2 * (conj (velocityCoeffT u i k r) * velocityDerivCoeffT u i k r).re

theorem hasDerivAt_critFreqEnergy {u : SpaceTimeField} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I)
    (k : PeriodicFrequency) :
    HasDerivAt (critFreqEnergy u k) (critFreqEnergyDeriv u k t) t := by
  have h : HasDerivAt (fun r ↦ ∑ i : Fin 3, ‖velocityCoeffT u i k r‖ ^ 2)
      (∑ i : Fin 3,
        2 * (conj (velocityCoeffT u i k t) * velocityDerivCoeffT u i k t).re) t :=
    HasDerivAt.fun_sum fun i _ ↦
      hasDerivAt_norm_sq_complex (hasDerivAt_velocityCoeffT hI hu ht i k)
  exact h.const_mul _

theorem homogeneousDatumWeight_half_sq (k : PeriodicFrequency) :
    homogeneousDatumWeight (1 / 2 : ℝ) k ^ 2 =
      Real.sqrt (periodicAngularFrequencySq k) := by
  by_cases hk : k = 0
  · subst hk
    have h0 : periodicAngularFrequencySq (0 : PeriodicFrequency) = 0 := by
      simp [periodicAngularFrequencySq]
    rw [NSFormalization.Section3.T13.homogeneousDatumWeight_zero, h0, Real.sqrt_zero]
    norm_num
  · have hA : (0 : ℝ) ≤ periodicAngularFrequencySq k := angularFrequencySq_nonneg k
    have hw : homogeneousDatumWeight (1 / 2 : ℝ) k
        = (periodicAngularFrequencySq k) ^ ((1 / 2 : ℝ) / 2) := by
      unfold homogeneousDatumWeight
      split_ifs
      rfl
    have hexp : (1 / 2 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
    rw [hw, ← Real.rpow_natCast ((periodicAngularFrequencySq k) ^ ((1 / 2 : ℝ) / 2)) 2,
      ← Real.rpow_mul hA, hexp, ← Real.sqrt_eq_rpow]

theorem homogeneousDatumWeight_three_halves_sq (k : PeriodicFrequency) :
    homogeneousDatumWeight (3 / 2 : ℝ) k ^ 2 =
      homogeneousDatumWeight (1 / 2 : ℝ) k ^ 2 * periodicAngularFrequencySq k := by
  rw [homogeneousDatumWeight_three_halves k, mul_pow, homogeneousDatumWeight_half_sq,
    Real.sq_sqrt (angularFrequencySq_nonneg k)]

theorem abs_critFreqEnergyDeriv_le_freq (u : SpaceTimeField) (k : PeriodicFrequency)
    (r : ℝ) :
    |critFreqEnergyDeriv u k r| ≤ |freqEnergyDerivT ((1 : ℕ) : ℝ) u k r| := by
  have hP : 0 < periodicFrequencyWeight k := periodicFrequencyWeight_pos k
  have hW : (0 : ℝ) ≤ homogeneousDatumWeight (1 / 2 : ℝ) k ^ 2 := sq_nonneg _
  have hone : periodicFrequencyWeight k ^ (((1 : ℕ) : ℝ)) = periodicFrequencyWeight k := by
    rw [Nat.cast_one, Real.rpow_one]
  have hle : homogeneousDatumWeight (1 / 2 : ℝ) k ^ 2 ≤
      periodicFrequencyWeight k ^ (((1 : ℕ) : ℝ)) := by
    rw [homogeneousDatumWeight_half_sq, hone]
    exact sqrt_angularFrequencySq_le_weight k
  rw [critFreqEnergyDeriv, freqEnergyDerivT, abs_mul, abs_mul, abs_of_nonneg hW,
    abs_of_nonneg (Real.rpow_nonneg hP.le _)]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

theorem abs_critFreqEnergyDeriv_le {u : SpaceTimeField} {r : ℝ}
    {A : PeriodicSobolev ((2 * 1 + 4 : ℕ) : ℝ)}
    (hA : IsPeriodicDatum ((2 * 1 + 4 : ℕ) : ℝ) (fun x ↦ u (r, x)) A)
    {M D : ℝ} (hM : ‖A‖ ≤ M)
    (hD : ∀ (i : Fin 3) (k : PeriodicFrequency), ‖velocityDerivCoeffT u i k r‖ ≤ D)
    (k : PeriodicFrequency) :
    |critFreqEnergyDeriv u k r| ≤ 6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹ :=
  (abs_critFreqEnergyDeriv_le_freq u k r).trans
    (abs_freqEnergyDerivT_le (m := 1) hA hM hD k)

theorem summable_critFreqEnergy {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) T) :
    Summable (fun k : PeriodicFrequency ↦ critFreqEnergy w.velocity k r) := by
  have hs : ContDiff ℝ ∞ (fun x : Space ↦ w.velocity (r, x)) :=
    classical_velocity_slice_contDiff w hr
  have hp : IsPeriodicSpatial (fun x : Space ↦ w.velocity (r, x)) :=
    w.velocity_periodic r hr
  exact NSFormalization.Section3.T13.summable_homogeneous_total
    (s := (1 / 2 : ℝ)) (by norm_num) hp hs

/-- **The order-`1/2` homogeneous energy profile is differentiable at every
interior time**, with derivative the termwise-differentiated Fourier series. -/
theorem hasDerivAt_tsum_critFreqEnergy {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r ↦ ∑' k : PeriodicFrequency, critFreqEnergy w.velocity k r)
      (∑' k : PeriodicFrequency, critFreqEnergyDeriv w.velocity k t) t := by
  classical
  have hI : IsOpen (Ioo (0 : ℝ) T) := isOpen_Ioo
  have hu : ContDiffOn ℝ ∞ w.velocity (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    w.velocity_smooth.mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  obtain ⟨ht0, htT⟩ := ht
  set α : ℝ := t / 2 with hαdef
  set β : ℝ := (t + T) / 2 with hβdef
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hαt : α < t := by rw [hαdef]; linarith
  have htβ : t < β := by rw [hβdef]; linarith
  have hβT : β < T := by rw [hβdef]; linarith
  have hJI : Icc α β ⊆ Ioo (0 : ℝ) T := fun x hx ↦
    ⟨lt_of_lt_of_le hα0 hx.1, lt_of_le_of_lt hx.2 hβT⟩
  have hSJ : Ioo α β ⊆ Icc α β := Ioo_subset_Icc_self
  have hSI : Ioo α β ⊆ Ioo (0 : ℝ) T := hSJ.trans hJI
  have htS : t ∈ Ioo α β := ⟨hαt, htβ⟩
  obtain ⟨D, hD0, hD⟩ := exists_velocityDerivCoeffT_bound hI hu isCompact_Icc hJI
  obtain ⟨G, hGc, hGd⟩ := w.sobolev (2 * 1 + 4)
  have hGsub : Icc α β ⊆ Ico (0 : ℝ) T := fun x hx ↦
    ⟨le_of_lt (lt_of_lt_of_le hα0 hx.1), lt_of_le_of_lt hx.2 hβT⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hGc.mono hGsub)
  have hsummable : Summable fun k : PeriodicFrequency ↦
      6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹ :=
    summable_inverse_periodicFrequencyWeight.mul_left _
  have hg0 : Summable fun k ↦ critFreqEnergy w.velocity k t :=
    summable_critFreqEnergy w ⟨le_of_lt ht0, htT⟩
  exact hasDerivAt_tsum_of_isPreconnected (u := fun k : PeriodicFrequency ↦
      6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹)
    (g := fun k ↦ critFreqEnergy w.velocity k)
    (g' := fun k r ↦ critFreqEnergyDeriv w.velocity k r)
    hsummable isOpen_Ioo isPreconnected_Ioo
    (fun k r hr ↦ hasDerivAt_critFreqEnergy hI hu (hSI hr) k)
    (fun k r hr ↦ by
      rw [Real.norm_eq_abs]
      exact abs_critFreqEnergyDeriv_le (hGd r (hGsub (hSJ hr))) (hM r (hSJ hr))
        (fun i k' ↦ hD r (hSJ hr) i k') k)
    htS hg0 htS

/-! ## §4  Homogeneous norms as datum norms, and the mean-free slice -/

theorem homENorm_eq_enorm_of_datum {s : ℝ} {z : SpatialField} {A : PeriodicSobolev s}
    (hA : IsPeriodicHomogeneousDatum s z A) :
    periodicHomogeneousENorm s z = ‖A‖ₑ := by
  refine le_antisymm ?_ ?_
  · exact iInf_le (fun B : {B : PeriodicSobolev s // IsPeriodicHomogeneousDatum s z B} ↦ ‖B.1‖ₑ)
      ⟨A, hA⟩
  · refine le_iInf fun B ↦ ?_
    rw [NSFormalization.Section3.T13.homogeneousDatum_unique B.1 A B.2 hA]

theorem homENorm_toReal_eq_norm {s : ℝ} {z : SpatialField} {A : PeriodicSobolev s}
    (hA : IsPeriodicHomogeneousDatum s z A) :
    (periodicHomogeneousENorm s z).toReal = ‖A‖ := by
  rw [homENorm_eq_enorm_of_datum hA, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]

theorem homENorm_toReal_sq {s : ℝ} (hs : 0 < s) {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfs : ContDiff ℝ ∞ f) :
    (periodicHomogeneousENorm s (meanZeroPartT f)).toReal ^ 2 =
      ∑' k : PeriodicFrequency, homogeneousDatumWeight s k ^ 2 *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2 := by
  obtain ⟨A, hA, hAnorm⟩ := NSFormalization.Section3.T13.exists_homogeneous_datum hs hfp hfs
  rw [homENorm_toReal_eq_norm hA, hAnorm]

theorem zero_mem_initialClassT : (fun _ : Space ↦ (0 : Space)) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x j
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

/-- `03-torus.tex:395-401`: along a classical solution from rest the untranslated
mean-free velocity slice **is** the mean-free part of the velocity slice (lane
389's `mean_formula`, `m(t) = ∫_{T³} u(t)`). -/
theorem meanFreeVelocity_slice_eq {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) T) :
    (fun x ↦ meanFreeVelocity g w.velocity (r, x)) =
      meanZeroPartT (fun x ↦ w.velocity (r, x)) := by
  have hmean : meanPathT g r = meanT (fun x ↦ w.velocity (r, x)) := by
    have hm := periodicMeanReductionAPI.mean_formula ν hν (fun _ : Space ↦ (0 : Space))
      zero_mem_initialClassT g hg T w r hr
    simpa [meanPathT, velocityMeanT, galileanMeanT, meanT_const] using hm.symm
  funext x
  simp [meanFreeVelocity, meanZeroPartT, hmean]

theorem meanFreeForce_slice_eq (g : SpaceTimeField) (r : ℝ) :
    (fun x ↦ meanFreeForce g (r, x)) = meanZeroPartT (fun x ↦ g (r, x)) := rfl

theorem criticalY_toReal_sq_eq_tsum {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) T) :
    (criticalY (meanFreeVelocity g w.velocity) r).toReal ^ 2 =
      ∑' k : PeriodicFrequency, critFreqEnergy w.velocity k r := by
  have hsmooth : ContDiff ℝ ∞ (fun x ↦ w.velocity (r, x)) :=
    classical_velocity_slice_contDiff w hr
  have hper : IsPeriodicSpatial (fun x ↦ w.velocity (r, x)) := w.velocity_periodic r hr
  show (periodicHomogeneousENorm (1 / 2)
      (fun x ↦ meanFreeVelocity g w.velocity (r, x))).toReal ^ 2 = _
  rw [meanFreeVelocity_slice_eq hν hg w hr,
    homENorm_toReal_sq (by norm_num : (0 : ℝ) < 1 / 2) hper hsmooth]
  rfl

theorem criticalZ_toReal_sq_eq_tsum {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) T) :
    (criticalZ (meanFreeVelocity g w.velocity) r).toReal ^ 2 =
      ∑' k : PeriodicFrequency, homogeneousDatumWeight (3 / 2) k ^ 2 *
        ∑ i : Fin 3, ‖velocityCoeffT w.velocity i k r‖ ^ 2 := by
  have hsmooth : ContDiff ℝ ∞ (fun x ↦ w.velocity (r, x)) :=
    classical_velocity_slice_contDiff w hr
  have hper : IsPeriodicSpatial (fun x ↦ w.velocity (r, x)) := w.velocity_periodic r hr
  show (periodicHomogeneousENorm (3 / 2)
      (fun x ↦ meanFreeVelocity g w.velocity (r, x))).toReal ^ 2 = _
  rw [meanFreeVelocity_slice_eq hν hg w hr,
    homENorm_toReal_sq (by norm_num : (0 : ℝ) < 3 / 2) hper hsmooth]
  rfl

/-- `03-torus.tex:407-411`: `(u·∇)u = (v·∇)v + (m·∇)v` for the untranslated
mean-free field `v = u - m(t)`. -/
theorem advection_mean_split {ν T : ℝ} {g : SpaceTimeField}
    (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T) (t : ℝ) (x : Space) :
    convectionFieldT w.velocity (t, x) =
      advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x +
        fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) := by
  have hfd : fderiv ℝ (fun y ↦ meanFreeVelocity g w.velocity (t, y)) x =
      fderiv ℝ (fun y ↦ w.velocity (t, y)) x := by
    have hrw : (fun y ↦ meanFreeVelocity g w.velocity (t, y)) =
        fun y ↦ w.velocity (t, y) - meanPathT g t := rfl
    rw [hrw, fderiv_sub_const]
  show fderiv ℝ (fun y ↦ w.velocity (t, y)) x (w.velocity (t, x)) = _
  show _ = fderiv ℝ (fun y ↦ meanFreeVelocity g w.velocity (t, y)) x
      (meanFreeVelocity g w.velocity (t, x)) + _
  rw [hfd]
  have hsub : meanFreeVelocity g w.velocity (t, x) = w.velocity (t, x) - meanPathT g t := rfl
  rw [hsub, map_sub, sub_add_cancel]

/-! ## §5  The frequency split of the differentiated energy -/

/-- The raw-coefficient form of T11's `freqEnergyDerivT_split` at order `0`: the
pressure term has dropped by coefficient-side solenoidality. -/
theorem rawEnergyDeriv_split {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) (hfp : IsPeriodicOn univ f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (k : PeriodicFrequency) :
    (∑ i : Fin 3, 2 * (conj (velocityCoeffT w.velocity i k t) *
        velocityDerivCoeffT w.velocity i k t).re) =
      -2 * ν * (periodicAngularFrequencySq k *
          ∑ i : Fin 3, ‖velocityCoeffT w.velocity i k t‖ ^ 2) +
        2 * (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
            velocityCoeffT f i k t).re -
        2 * (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
            velocityCoeffT (convectionFieldT w.velocity) i k t).re := by
  have htI : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hvs : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) := classical_velocity_slice_contDiff w htI
  have hvp : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t htI
  obtain ⟨Gm, hGm⟩ := exists_periodicDatum_smooth ((0 : ℕ) : ℝ) hvs hvp
  obtain ⟨Fm, hFm⟩ := exists_force_datum hf hfp ((0 : ℕ) : ℝ) t
  obtain ⟨Nm, hNm⟩ := exists_convection_datum w ((0 : ℕ) : ℝ) htI
  have hsplit := freqEnergyDerivT_split w hf ht 0 hGm hFm hNm k
  have hone : periodicFrequencyWeight k ^ (((0 : ℕ) : ℝ)) = 1 := by
    rw [Nat.cast_zero, Real.rpow_zero]
  rw [freqEnergyDerivT, hone, one_mul, datum_pair_entry hGm hFm k,
    datum_pair_entry hGm hNm k, hone] at hsplit
  simpa using hsplit

private theorem re_conj_mul_comm (a b : ℂ) : (conj a * b).re = (conj b * a).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring


/-! ## §6  `eq:criticalenergy` -/

/-- **T20 U8, `03-torus.tex:420-440` (`eq:criticalenergy`).**  For the zero
initial datum and `g ∈ F_T`, at every interior time of the classical lifespan the
squared critical norm `y² = ‖v‖²_{Ḣ^{1/2}}` of the untranslated mean-free
velocity has an actual derivative `E'`, and

`E'/2 + (ν - C₀ y) z² ≤ b y`,  `C₀ = criticalTrilinearConst`.

This is the `criticalEnergy` field of `CriticalRegularityTAPI` verbatim. -/
theorem criticalEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ E' : ℝ,
            HasDerivAt
                (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
                E' t ∧
              E' / 2 +
                  (ν - criticalTrilinearConst *
                    (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
                    (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 ≤
                (criticalB (meanFreeForce g) t).toReal *
                  (criticalY (meanFreeVelocity g w.velocity) t).toReal := by
  intro ν hν g hg T w t ht
  have htI : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hgm : MemForceT g := hg
  have hus : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) := classical_velocity_slice_contDiff w htI
  have hup : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t htI
  have hgs : ContDiff ℝ ∞ (fun x ↦ g (t, x)) := hgm.1.comp (contDiff_const.prodMk contDiff_id)
  have hgp : IsPeriodicSpatial (fun x ↦ g (t, x)) := hgm.2.1 t (mem_univ _)
  have hveq : (fun x ↦ meanFreeVelocity g w.velocity (t, x))
      = meanZeroPartT (fun x ↦ w.velocity (t, x)) := meanFreeVelocity_slice_eq hν hg w htI
  have hreg := reductionRegular ν hν g hg T w t htI
  have hvSP : SmoothPeriodicT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.2.1
  have hvH : MemPeriodicHomogeneous (1 / 2) (fun x ↦ meanFreeVelocity g w.velocity (t, x)) :=
    hreg.2.2.1
  have hvH3 : MemPeriodicHomogeneous (3 / 2) (fun x ↦ meanFreeVelocity g w.velocity (t, x)) :=
    hreg.2.2.2.1
  obtain ⟨Lv, hL⟩ := lambda_exists _ hvSP
  obtain ⟨Av, hAv, -⟩ := NSFormalization.Section3.T13.exists_homogeneous_datum
    (show (0 : ℝ) < 1 / 2 by norm_num) hup hus
  obtain ⟨Bh, hBh, -⟩ := NSFormalization.Section3.T13.exists_homogeneous_datum
    (show (0 : ℝ) < 1 / 2 by norm_num) hgp hgs
  -- Off the zero mode the mean-free coefficients are the raw coefficients.
  have hvcoeff : ∀ (i : Fin 3) {k : PeriodicFrequency}, k ≠ 0 →
      periodicFourierCoeff (fun x ↦ ((meanFreeVelocity g w.velocity (t, x) i : ℝ) : ℂ)) k =
        velocityCoeffT w.velocity i k t := by
    intro i k hk
    have hfun : (fun x ↦ ((meanFreeVelocity g w.velocity (t, x) i : ℝ) : ℂ)) =
        (fun x ↦ ((meanZeroPartT (fun y ↦ w.velocity (t, y)) x i : ℝ) : ℂ)) := by
      funext x
      rw [show meanFreeVelocity g w.velocity (t, x) =
        meanZeroPartT (fun y ↦ w.velocity (t, y)) x from congrFun hveq x]
    rw [hfun]
    exact NSFormalization.Section3.T13.periodicFourierCoeff_meanZeroPart hus.continuous i hk
  -- `y` and `b` as datum norms.
  have hy : (criticalY (meanFreeVelocity g w.velocity) t).toReal = ‖Av‖ := by
    show (periodicHomogeneousENorm (1 / 2)
      (fun x ↦ meanFreeVelocity g w.velocity (t, x))).toReal = _
    rw [hveq, homENorm_toReal_eq_norm hAv]
  have hb : (criticalB (meanFreeForce g) t).toReal = ‖Bh‖ := by
    show (periodicHomogeneousENorm (1 / 2) (fun x ↦ meanFreeForce g (t, x))).toReal = _
    rw [meanFreeForce_slice_eq g t, homENorm_toReal_eq_norm hBh]
  -- Dissipation.
  have hsumZ : Summable (fun k : PeriodicFrequency ↦
      homogeneousDatumWeight (3 / 2) k ^ 2 *
        ∑ i : Fin 3, ‖velocityCoeffT w.velocity i k t‖ ^ 2) :=
    NSFormalization.Section3.T13.summable_homogeneous_total (s := (3 / 2 : ℝ)) (by norm_num)
      hup hus
  have hdiss : HasSum (fun k : PeriodicFrequency ↦
      homogeneousDatumWeight (1 / 2) k ^ 2 * periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖velocityCoeffT w.velocity i k t‖ ^ 2)
      ((criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2) := by
    rw [criticalZ_toReal_sq_eq_tsum hν hg w htI]
    exact hsumZ.hasSum.congr_fun fun k ↦ by rw [homogeneousDatumWeight_three_halves_sq]
  -- Force pairing, Cauchy–Schwarz on the coefficient side.
  have hforce : HasSum (fun k : PeriodicFrequency ↦
      homogeneousDatumWeight (1 / 2) k ^ 2 *
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT g i k t).re)
      (torusRealPairing Av Bh) := by
    refine (hasSum_datum_pair Av Bh).congr_fun fun k ↦ ?_
    by_cases hk : k = 0
    · subst hk
      have hAv0 : ∀ i : Fin 3, Av.1 i 0 = 0 := by
        intro i
        rw [hAv.2.2.2 i 0, NSFormalization.Section3.T13.homogeneousDatumWeight_zero]
        simp
      simp [hAv0, NSFormalization.Section3.T13.homogeneousDatumWeight_zero]
    · have hcv : ∀ i : Fin 3, Av.1 i k =
          ((homogeneousDatumWeight (1 / 2) k : ℝ) : ℂ) * velocityCoeffT w.velocity i k t := by
        intro i
        rw [hAv.2.2.2 i k, smul_eq_mul]
        congr 1
        exact NSFormalization.Section3.T13.periodicFourierCoeff_meanZeroPart hus.continuous i hk
      have hch : ∀ i : Fin 3, Bh.1 i k =
          ((homogeneousDatumWeight (1 / 2) k : ℝ) : ℂ) * velocityCoeffT g i k t := by
        intro i
        rw [hBh.2.2.2 i k, smul_eq_mul]
        congr 1
        exact NSFormalization.Section3.T13.periodicFourierCoeff_meanZeroPart hgs.continuous i hk
      have hterm : (∑ i : Fin 3, conj (Av.1 i k) * Bh.1 i k) =
          ((homogeneousDatumWeight (1 / 2) k ^ 2 : ℝ) : ℂ) *
            ∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT g i k t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hcv i, hch i, map_mul, Complex.conj_ofReal]
        push_cast
        ring
      rw [hterm, Complex.re_ofReal_mul]
  -- Convection pairing, through torus Parseval and the constant-transport drop.
  have hNvS : ContDiff ℝ ∞ (fun x ↦ advection
      (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) :=
    @advection_spatial_contDiff (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 hvSP.1
  have hNvP : IsPeriodicSpatial (fun x ↦ advection
      (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) :=
    @advection_spatial_periodic (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 hvSP.2
  have hus1 : ContDiff ℝ 1 (fun y ↦ w.velocity (t, y)) := hus.of_le (by simp)
  have hDcont : ∀ i : Fin 3, Continuous
      (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i :
        ℝ) : ℂ)) := by
    intro i
    have hrw : (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i :
          ℝ) : ℂ))
        = fun x ↦ ∑ j : Fin 3, ((meanPathT g t j : ℝ) : ℂ) *
            (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (coordinateVector j) : Space) i :
              ℝ) : ℂ) :=
      funext fun x ↦ ofReal_fderiv_dir_component _ _ i x
    rw [hrw]
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
      (Complex.continuous_ofReal.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
        (NavierStokes.PeriodicIntegration.continuous_partial hus1 j)))
  have hNcoeff : ∀ (i : Fin 3) (k : PeriodicFrequency),
      velocityCoeffT (convectionFieldT w.velocity) i k t =
        periodicFourierCoeff (fun x ↦ ((advection
          (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ)) k +
          periodicFourierCoeff (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x
            (meanPathT g t) : Space) i : ℝ) : ℂ)) k := by
    intro i k
    have hfun : (fun x ↦ ((convectionFieldT w.velocity (t, x) i : ℝ) : ℂ)) =
        (fun x ↦ ((advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i :
            ℝ) : ℂ)) +
          (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i :
            ℝ) : ℂ)) := by
      funext x
      show ((convectionFieldT w.velocity (t, x) i : ℝ) : ℂ) =
        ((advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ) +
          (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i : ℝ) : ℂ)
      rw [advection_mean_split w t x]
      simp
    show periodicFourierCoeff (fun x ↦ ((convectionFieldT w.velocity (t, x) i : ℝ) : ℂ)) k = _
    rw [hfun]
    exact NSFormalization.Paper1.periodicFourierCoeff_add
      (continuous_component_ofReal hNvS.continuous i) (hDcont i) k
  have hconv : HasSum (fun k : PeriodicFrequency ↦
      homogeneousDatumWeight (1 / 2) k ^ 2 *
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
          velocityCoeffT (convectionFieldT w.velocity) i k t).re)
      (periodicPairing
        (fun x ↦ advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) Lv) := by
    refine (hasSum_periodicPairing ⟨hNvS, hNvP⟩ hL.1).congr_fun fun k ↦ ?_
    have hRHS : (∑ i : Fin 3,
        conj (periodicFourierCoeff (fun x ↦ ((advection
            (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ)) k) *
          periodicFourierCoeff (fun x ↦ ((Lv x i : ℝ) : ℂ)) k)
        = ((Real.sqrt (periodicAngularFrequencySq k) : ℝ) : ℂ) *
            ∑ i : Fin 3,
              conj (periodicFourierCoeff (fun x ↦ ((advection
                (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ)) k) *
                periodicFourierCoeff
                  (fun x ↦ ((meanFreeVelocity g w.velocity (t, x) i : ℝ) : ℂ)) k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hL.2 i k]
      ring
    rw [hRHS, Complex.re_ofReal_mul, ← homogeneousDatumWeight_half_sq]
    by_cases hk : k = 0
    · subst hk
      rw [NSFormalization.Section3.T13.homogeneousDatumWeight_zero]
      ring
    · congr 1
      have hDzero : (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
          periodicFourierCoeff (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x
            (meanPathT g t) : Space) i : ℝ) : ℂ)) k).re = 0 :=
        re_sum_conj_fderiv_dir_zero hus hup (meanPathT g t) k
      have hstep : ∀ i : Fin 3,
          conj (velocityCoeffT w.velocity i k t) *
              velocityCoeffT (convectionFieldT w.velocity) i k t =
            conj (velocityCoeffT w.velocity i k t) *
                periodicFourierCoeff (fun x ↦ ((advection
                  (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ)) k +
              conj (velocityCoeffT w.velocity i k t) *
                periodicFourierCoeff (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x
                  (meanPathT g t) : Space) i : ℝ) : ℂ)) k := by
        intro i
        rw [hNcoeff i k]
        ring
      rw [Finset.sum_congr rfl (fun i _ ↦ hstep i), Finset.sum_add_distrib, Complex.add_re,
        hDzero, add_zero, Complex.re_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hvcoeff i hk, re_conj_mul_comm]
  -- The differentiated critical energy, summed.
  have hcomb : HasSum (fun k : PeriodicFrequency ↦ critFreqEnergyDeriv w.velocity k t)
      (-2 * ν * (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 +
        2 * torusRealPairing Av Bh -
        2 * periodicPairing (fun x ↦ advection
          (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) Lv) := by
    have hsum := ((hdiss.mul_left (-2 * ν)).add (hforce.mul_left 2)).sub (hconv.mul_left 2)
    refine hsum.congr_fun fun k ↦ ?_
    simp only [critFreqEnergyDeriv]
    rw [rawEnergyDeriv_split w hgm.1 hgm.2.1 ht k]
    ring
  have hE := hcomb.tsum_eq
  have hderiv := hasDerivAt_tsum_critFreqEnergy w ht
  have hev : (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
      =ᶠ[nhds t] (fun r ↦ ∑' k : PeriodicFrequency, critFreqEnergy w.velocity k r) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact criticalY_toReal_sq_eq_tsum hν hg w ⟨hr.1.le, hr.2⟩
  refine ⟨∑' k : PeriodicFrequency, critFreqEnergyDeriv w.velocity k t,
    hderiv.congr_of_eventuallyEq hev, ?_⟩
  rw [hE]
  have hP : torusRealPairing Av Bh ≤
      (criticalB (meanFreeForce g) t).toReal *
        (criticalY (meanFreeVelocity g w.velocity) t).toReal := by
    rw [hy, hb, mul_comm]
    exact torusRealPairing_le Av Bh
  have hU7 : |periodicPairing (fun x ↦ advection
        (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) Lv| ≤
      criticalTrilinearConst * (criticalY (meanFreeVelocity g w.velocity) t).toReal *
        (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 :=
    criticalTrilinear_pairing (fun x ↦ meanFreeVelocity g w.velocity (t, x)) Lv hvSP hvH hvH3 hL
  have hQ : -periodicPairing (fun x ↦ advection
        (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) Lv ≤
      criticalTrilinearConst * (criticalY (meanFreeVelocity g w.velocity) t).toReal *
        (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 :=
    (neg_le_abs _).trans hU7
  have hexpand : (ν - criticalTrilinearConst *
        (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
        (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 =
      ν * (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 -
        criticalTrilinearConst * (criticalY (meanFreeVelocity g w.velocity) t).toReal *
          (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 := by ring
  rw [hexpand]
  linarith [hP, hQ]

end NSFormalization.Section3.T20
