import NSFormalization.Source.FourierConvention
import NSFormalization.Paper3.SobolevWeights
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# B02, units 3 and 4: the low-frequency weight and the angular `L¹ → L∞` bound

This module discharges three obligation fields of `research/B02/Spec.lean`'s
`HomogeneousApproxAPI`, the low/high-frequency split of `eq:Rnegative-cutoff`
(`paper/sections/04-whole-space.tex:241-249`):

* `lowFrequencyIntegrable` (spec `:370`): the low-frequency homogeneous weight
  `|ξ|^{2s}` is integrable on the unit ball exactly when `-3/2 < s`.  This is the
  finiteness remark "The integral at the origin is finite in dimension three"
  (`04-whole-space.tex:249`).
* `lowFrequencyIntegral` (spec `:379`): the exact value of that integral at the
  manuscript's order `s = -1`, `∫_{|ξ|<1}|ξ|^{-2}dξ = 4π`
  (`04-whole-space.tex:246`), which turns the unnamed constant `C'` into the
  explicit `1/(2π²)`.
* `fourierSupBound` (spec `:397`): the manuscript's `C`, the `L¹ → L∞` bound for
  the unitary angular transform of `01-introduction.tex:91`, in the **vector**
  form `(Σ_i|ẑ_i(ξ)|²)^{1/2} ≤ (2π)^{-3/2}∫‖z‖` (`04-whole-space.tex:246`).

## What is reused

* `NSFormalization.Paper3.homogeneous_low_frequency_integrable`
  (`Paper3/SobolevWeights.lean:54`) at the constant profile `φ ≡ 1`, `C = 1`, for
  `lowFrequencyIntegrable`.
* `MeasureTheory.integral_fun_norm_addHaar`
  (`Mathlib/.../HaarToSphere.lean:296`) plus `EuclideanSpace.volume_ball_fin_three`
  for the exact value `4π`.
* `angularFourier` / `angularFourier_eq_integral`
  (`Source/FourierConvention.lean:23,27`) for the honest integral form of the
  transform, and `MeasureTheory.norm_integral_le_integral_norm` on the
  `EuclideanSpace ℂ (Fin 3)`-valued integrand for the sup bound (the vector form,
  which avoids the spurious factor `3` a componentwise bound would cost).

`SpatialField = Space → Space` (`verification/Contracts/V1/Data.lean:99`) cannot
be imported here, so `fourierSupBound` is stated with the definitionally equal
`Space → Space`; `research/B02/axioms_u34.lean` checks the match against the spec
field type.
-/

open MeasureTheory NavierStokes.ProblemStatement NSFormalization.Source

noncomputable section

namespace NSFormalization.Section4.B02

/-- `research/B02/Spec.lean:370` `lowFrequencyIntegrable`, `04-whole-space.tex:249`:
the low-frequency homogeneous weight `|ξ|^{2s}` is integrable on the unit ball of
`R³` exactly in the range `-3/2 < s` (i.e. `2s > -3`).  Obtained from
`Paper3.homogeneous_low_frequency_integrable` at the constant profile `φ ≡ 1`. -/
theorem lowFrequencyIntegrable (s : ℝ) (hs : -3 / 2 < s) :
    IntegrableOn (fun ξ : Space => ‖ξ‖ ^ (2 * s)) (Metric.ball (0 : Space) 1) volume := by
  have h := NSFormalization.Paper3.homogeneous_low_frequency_integrable (s := s) (C := 1)
    hs (φ := fun _ => (1 : ℂ)) measurable_const (by norm_num) (fun ξ => by simp)
  simpa using h

/-- `research/B02/Spec.lean:379` `lowFrequencyIntegral`, `04-whole-space.tex:246`:
the factor `∫_{|ξ|<1}|ξ|^{-2}dξ` of `eq:Rnegative-cutoff` evaluated in dimension
three at the manuscript's order `s = -1` is `∫₀¹ r^{-2}·4πr² dr = 4π`.  The radial
reduction is `integral_fun_norm_addHaar`; the ball volume `4π/3` in `R³` is
`EuclideanSpace.volume_ball_fin_three`, and `3·(4π/3) = 4π`. -/
theorem lowFrequencyIntegral :
    (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * (-1 : ℝ))) = 4 * Real.pi := by
  set g : ℝ → ℝ := (Set.Iio 1).indicator (fun t => t ^ (2 * (-1 : ℝ))) with hg
  -- Rewrite the ball integral as `∫ ξ, g ‖ξ‖` (radial function of the norm).
  have hset : (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * (-1 : ℝ)))
      = ∫ ξ : Space, g ‖ξ‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with ξ
    by_cases h : ξ ∈ Metric.ball (0 : Space) 1
    · have h' : ‖ξ‖ ∈ Set.Iio (1 : ℝ) := by
        simpa [Set.mem_Iio, Metric.mem_ball, dist_zero_right] using h
      rw [Set.indicator_of_mem h, hg, Set.indicator_of_mem h']
    · have h' : ‖ξ‖ ∉ Set.Iio (1 : ℝ) := by
        simpa [Set.mem_Iio, Metric.mem_ball, dist_zero_right] using h
      rw [Set.indicator_of_notMem h, hg, Set.indicator_of_notMem h']
  rw [hset, integral_fun_norm_addHaar volume g]
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space, finrank_euclideanSpace]
  -- The unit-ball volume of `R³` is `4π/3`.
  have hvol : (volume : Measure Space).real (Metric.ball 0 1) = Real.pi * 4 / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  -- On `(0,1)` the radial integrand `r^{n-1}·g r = r²·r^{-2}` collapses to `1`.
  have hEqOn : Set.EqOn (fun y : ℝ => y ^ (2 : ℕ) * y ^ (2 * (-1 : ℝ)))
      (fun _ => (1 : ℝ)) (Set.Ioo 0 1) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy.1
    show y ^ (2 : ℕ) * y ^ (2 * (-1 : ℝ)) = 1
    rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy0,
      show ((2 : ℕ) : ℝ) + 2 * (-1 : ℝ) = 0 by norm_num, Real.rpow_zero]
  have hinner : (∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ Space - 1) • g y) = 1 := by
    rw [hdim]
    have hstep : (∫ y in Set.Ioi (0 : ℝ), y ^ (3 - 1) • g y)
        = ∫ y in Set.Ioi (0 : ℝ),
            (Set.Iio 1).indicator (fun t => t ^ (2 : ℕ) * t ^ (2 * (-1 : ℝ))) y := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Set.Iio (1 : ℝ)
      · simp only [hg, Set.indicator_of_mem hy, smul_eq_mul]
      · simp only [hg, Set.indicator_of_notMem hy, smul_zero]
    rw [hstep, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
      setIntegral_congr_fun measurableSet_Ioo hEqOn]
    simp
  rw [hinner, hdim, hvol]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- `research/B02/Spec.lean:397` `fourierSupBound`, `04-whole-space.tex:246` /
`01-introduction.tex:91,103`: the `L¹ → L∞` bound for the unitary angular
transform, in the **vector** form
`(Σ_i ‖ẑ_i(ξ)‖²)^{1/2} ≤ (2π)^{-3/2} ∫‖z‖`.  The proof forms the
`EuclideanSpace ℂ (Fin 3)`-valued integrand `x ↦ e^{-ix·ξ}·z(x)` (whose norm is
`‖z(x)‖`, the phase being unimodular) and applies `norm_integral_le_integral_norm`;
this is the triangle inequality for the vector Bochner integral, which — unlike a
componentwise `L¹→L∞` bound — carries no spurious factor `3`. -/
theorem fourierSupBound (k : Space → Space) (hk : MemLp k 1 volume) (ξ : Space) :
    Real.sqrt (∑ i : Fin 3, ‖angularFourier (fun x : Space => ((k x i : ℝ) : ℂ)) ξ‖ ^ 2) ≤
      (2 * Real.pi) ^ (-(3 : ℝ) / 2) * ∫ x : Space, ‖k x‖ := by
  have hInt : Integrable k volume := (memLp_one_iff_integrable).mp hk
  -- The angular phase `e^{-i⟪x,ξ⟫}` is unimodular.
  have hnorm_e : ∀ x : Space, ‖Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    intro x
    rw [show (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)
          = (((-(inner ℝ x ξ) : ℝ) : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  -- The complexified, phase-modulated vector field, valued in `EuclideanSpace ℂ (Fin 3)`.
  set G : Space → EuclideanSpace ℂ (Fin 3) :=
    fun x => (EuclideanSpace.equiv (Fin 3) ℂ).symm (fun i => ((k x i : ℝ) : ℂ)) with hG_def
  set F : Space → EuclideanSpace ℂ (Fin 3) :=
    fun x => Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I) • G x with hF_def
  have hFxi : ∀ x i, F x i
      = Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I) • ((k x i : ℝ) : ℂ) := fun x i => rfl
  -- `‖F x‖ = ‖k x‖` because the phase is unimodular and `‖↑(k x i)‖ = ‖k x i‖`.
  have hFx_norm : ∀ x, ‖F x‖ = ‖k x‖ := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq (k x)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hFxi x i, norm_smul, hnorm_e x, one_mul, Complex.norm_real, Real.norm_eq_abs]
  -- `F` is a.e. strongly measurable and (being bounded by the integrable `‖k‖`) integrable.
  have hCplx : Continuous (fun v : Space => (fun i => ((v i : ℝ) : ℂ))) :=
    continuous_pi (fun i => Complex.continuous_ofReal.comp
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous)
  have hG_aesm : AEStronglyMeasurable G volume :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_aestronglyMeasurable
      (hCplx.comp_aestronglyMeasurable hInt.aestronglyMeasurable)
  have he : Continuous (fun x : Space => Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).neg.mul
        continuous_const)
  have hF_aesm : AEStronglyMeasurable F volume := he.aestronglyMeasurable.smul hG_aesm
  have hF_int : Integrable F volume :=
    (hInt.norm).mono' hF_aesm (Filter.Eventually.of_forall (fun x => (hFx_norm x).le))
  -- The `i`-th coordinate of the vector integral is the scalar Fourier integral.
  have hcomp : ∀ i, (∫ x, F x) i
      = ∫ x, Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I) • ((k x i : ℝ) : ℂ) := by
    intro i
    have h1 : (∫ x, F x) i = ∫ x, (F x) i := by
      simpa using ((EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm hF_int).symm
    rw [h1]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hFxi x i))
  -- `angularFourier` of each component is the amplitude times that coordinate.
  have hAFval : ∀ i, angularFourier (fun x => ((k x i : ℝ) : ℂ)) ξ
      = frequencyUnit ^ (-3 / 2 : ℝ) • ((∫ x, F x) i) := by
    intro i
    rw [angularFourier_eq_integral, ← hcomp i]
  -- Pull the amplitude out of the sum of squares.
  have hsum : (∑ i : Fin 3, ‖angularFourier (fun x => ((k x i : ℝ) : ℂ)) ξ‖ ^ 2)
      = (frequencyUnit ^ (-3 / 2 : ℝ)) ^ 2 * ∑ i, ‖(∫ x, F x) i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hAFval i, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hsum, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (Real.rpow_nonneg frequencyUnit_pos.le _),
    ← EuclideanSpace.norm_eq (∫ x, F x)]
  -- `‖∫ F‖ ≤ ∫ ‖F‖ = ∫ ‖k‖` by the vector triangle inequality.
  have hbound : ‖∫ x, F x‖ ≤ ∫ x, ‖k x‖ :=
    (norm_integral_le_integral_norm F).trans
      (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hFx_norm)))
  have hfreq : frequencyUnit ^ (-3 / 2 : ℝ) = (2 * Real.pi) ^ (-(3 : ℝ) / 2) := by
    unfold frequencyUnit; norm_num
  rw [hfreq]
  exact mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)

end NSFormalization.Section4.B02
