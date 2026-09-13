import Formal.R3StokesH2H3Smoothing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace MNS2

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal FourierTransform Topology

noncomputable section

theorem r3StokesScalarComplex_add_time
    (nu t s : ℝ) (xi : R3) :
    r3StokesScalarComplex nu (t + s) xi =
      r3StokesScalarComplex nu t xi * r3StokesScalarComplex nu s xi := by
  simp [r3StokesScalarComplex, r3StokesScalar_add_time]

theorem r3StokesL2FrequencyMultiplier_add_time
    {nu t s : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    r3StokesL2FrequencyMultiplier hnu (add_nonneg ht hs) =
      (r3StokesL2FrequencyMultiplier hnu ht).comp
        (r3StokesL2FrequencyMultiplier hnu hs) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards
    [r3StokesL2FrequencyMultiplier_ae hnu (add_nonneg ht hs) f,
      r3StokesL2FrequencyMultiplier_ae hnu ht
        (r3StokesL2FrequencyMultiplier hnu hs f),
      r3StokesL2FrequencyMultiplier_ae hnu hs f]
    with xi hleft houter hinner
  rw [hleft, ContinuousLinearMap.comp_apply, houter, hinner, smul_smul]
  rw [r3StokesScalarComplex_add_time]

theorem r3StokesL2Operator_add_time
    {nu t s : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    r3StokesL2Operator hnu (add_nonneg ht hs) =
      (r3StokesL2Operator hnu ht).comp (r3StokesL2Operator hnu hs) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change
    𝓕 (r3StokesL2Operator hnu (add_nonneg ht hs) f) =
      𝓕 ((r3StokesL2Operator hnu ht).comp
        (r3StokesL2Operator hnu hs) f)
  rw [fourier_r3StokesL2Operator, ContinuousLinearMap.comp_apply,
    fourier_r3StokesL2Operator, fourier_r3StokesL2Operator,
    r3StokesL2FrequencyMultiplier_add_time]
  rfl

theorem norm_r3StokesScalarLpTop_le_one
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    ‖r3StokesScalarLpTop hnu ht‖ ≤ 1 := by
  unfold r3StokesScalarLpTop
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (eLpNormEssSup_le_of_ae_bound
      (ae_of_all _ (norm_r3StokesScalarComplex_le_one hnu ht)))

theorem norm_r3StokesL2FrequencyMultiplier_apply_le
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) (f : R3L2Velocity) :
    ‖r3StokesL2FrequencyMultiplier hnu ht f‖ ≤ ‖f‖ := by
  calc
    ‖r3StokesL2FrequencyMultiplier hnu ht f‖ ≤
        ‖r3StokesScalarLpTop hnu ht‖ * ‖f‖ := Lp.norm_smul_le _ _
    _ ≤ 1 * ‖f‖ := by
      gcongr
      exact norm_r3StokesScalarLpTop_le_one hnu ht
    _ = ‖f‖ := one_mul _

theorem norm_r3StokesL2Operator_apply_le
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) (f : R3L2Velocity) :
    ‖r3StokesL2Operator hnu ht f‖ ≤ ‖f‖ := by
  calc
    ‖r3StokesL2Operator hnu ht f‖ = ‖𝓕 (r3StokesL2Operator hnu ht f)‖ := by
      symm
      exact Lp.norm_fourier_eq _
    _ = ‖r3StokesL2FrequencyMultiplier hnu ht (𝓕 f)‖ := by
      rw [fourier_r3StokesL2Operator]
    _ ≤ ‖𝓕 f‖ := norm_r3StokesL2FrequencyMultiplier_apply_le hnu ht _
    _ = ‖f‖ := Lp.norm_fourier_eq _

theorem norm_r3L2_eq_sqrt_integral_norm_sq (g : R3L2Velocity) :
    ‖g‖ = Real.sqrt (∫ xi : R3, ‖g xi‖ ^ 2) := by
  rw [Lp.norm_def,
    (Lp.memLp g).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [Real.sqrt_eq_rpow]
  exact Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _

theorem continuous_r3StokesL2FrequencyMultiplier_orbit
    {nu : ℝ} (hnu : 0 ≤ nu) (f : R3L2Velocity) :
    Continuous (fun t : Set.Ici (0 : ℝ) =>
      r3StokesL2FrequencyMultiplier hnu t.property f) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let F : Set.Ici (0 : ℝ) → R3 → ℝ := fun t xi =>
    ‖(r3StokesScalarComplex nu t xi -
      r3StokesScalarComplex nu t0 xi) • f xi‖ ^ 2
  have h_integral :
      Tendsto (fun t => ∫ xi : R3, F t xi) (𝓝 t0) (𝓝 0) := by
    have hDCT := tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝 t0) (F := F) (f := fun _ : R3 => (0 : ℝ))
      (bound := fun xi : R3 => 4 * ‖f xi‖ ^ 2)
      (by
        filter_upwards [] with t
        have hm : AEStronglyMeasurable
            (fun xi : R3 =>
              r3StokesScalarComplex nu t xi -
                r3StokesScalarComplex nu t0 xi) volume :=
          ((continuous_r3StokesScalarComplex nu t).sub
            (continuous_r3StokesScalarComplex nu t0)).aestronglyMeasurable
        have hv : AEStronglyMeasurable
            (fun xi : R3 =>
              (r3StokesScalarComplex nu t xi -
                r3StokesScalarComplex nu t0 xi) • f xi) volume :=
          hm.smul (Lp.aestronglyMeasurable f)
        exact (hv.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      (by
        filter_upwards [] with t
        exact ae_of_all _ fun xi => by
          rw [show F t xi =
              ‖(r3StokesScalarComplex nu t xi -
                r3StokesScalarComplex nu t0 xi) • f xi‖ ^ 2 by rfl,
            Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hdiff :
              ‖r3StokesScalarComplex nu t xi -
                r3StokesScalarComplex nu t0 xi‖ ≤ 2 := by
            calc
              _ ≤ ‖r3StokesScalarComplex nu t xi‖ +
                  ‖r3StokesScalarComplex nu t0 xi‖ := norm_sub_le _ _
              _ ≤ 1 + 1 := add_le_add
                (norm_r3StokesScalarComplex_le_one hnu t.property xi)
                (norm_r3StokesScalarComplex_le_one hnu t0.property xi)
              _ = 2 := by norm_num
          have hsmul :
              ‖(r3StokesScalarComplex nu t xi -
                r3StokesScalarComplex nu t0 xi) • f xi‖ ≤
                  2 * ‖f xi‖ := by
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
          calc
            _ ≤ (2 * ‖f xi‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hsmul 2
            _ = 4 * ‖f xi‖ ^ 2 := by ring)
      (by
        exact ((Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul 4)
      (by
        exact ae_of_all _ fun xi => by
          have htime : Continuous
              (fun t : Set.Ici (0 : ℝ) =>
                r3StokesScalarComplex nu t xi) := by
            unfold r3StokesScalarComplex r3StokesScalar r3StokesDecayRate
            fun_prop
          have hdiff : Tendsto
              (fun t : Set.Ici (0 : ℝ) =>
                r3StokesScalarComplex nu t xi -
                  r3StokesScalarComplex nu t0 xi)
              (𝓝 t0) (𝓝 0) := by
            have hc : ContinuousAt
                (fun _ : Set.Ici (0 : ℝ) =>
                  r3StokesScalarComplex nu t0 xi) t0 :=
              continuousAt_const
            have hdc := htime.continuousAt.sub hc
            change Tendsto
              (fun t : Set.Ici (0 : ℝ) =>
                r3StokesScalarComplex nu t xi -
                  r3StokesScalarComplex nu t0 xi)
              (𝓝 t0)
              (𝓝 (r3StokesScalarComplex nu t0 xi -
                r3StokesScalarComplex nu t0 xi)) at hdc
            simpa using hdc
          simpa [F] using ((hdiff.smul_const (f xi)).norm.pow 2))
    simpa [F] using hDCT
  have hnorm : ∀ t : Set.Ici (0 : ℝ),
      ‖r3StokesL2FrequencyMultiplier hnu t.property f -
        r3StokesL2FrequencyMultiplier hnu t0.property f‖ =
        Real.sqrt (∫ xi : R3, F t xi) := by
    intro t
    rw [norm_r3L2_eq_sqrt_integral_norm_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards
      [Lp.coeFn_sub
        (r3StokesL2FrequencyMultiplier hnu t.property f)
        (r3StokesL2FrequencyMultiplier hnu t0.property f),
        r3StokesL2FrequencyMultiplier_ae hnu t.property f,
        r3StokesL2FrequencyMultiplier_ae hnu t0.property f]
      with xi hsub ht ht0
    rw [hsub, Pi.sub_apply, ht, ht0, ← sub_smul]
  have hnorm_tendsto : Tendsto
      (fun t : Set.Ici (0 : ℝ) =>
        ‖r3StokesL2FrequencyMultiplier hnu t.property f -
          r3StokesL2FrequencyMultiplier hnu t0.property f‖)
      (𝓝 t0) (𝓝 0) := by
    have hsqrt : Tendsto
        (fun t : Set.Ici (0 : ℝ) => Real.sqrt (∫ xi : R3, F t xi))
        (𝓝 t0) (𝓝 0) := by
      have hsqrt0 : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hsqrtAt : ContinuousAt Real.sqrt (0 : ℝ) :=
          Real.continuous_sqrt.continuousAt
        change Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) at hsqrtAt
        simpa using hsqrtAt
      exact hsqrt0.comp h_integral
    simpa only [hnorm] using hsqrt
  apply tendsto_sub_nhds_zero_iff.mp
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto

theorem continuous_r3StokesL2Operator_orbit
    {nu : ℝ} (hnu : 0 ≤ nu) (f : R3L2Velocity) :
    Continuous (fun t : Set.Ici (0 : ℝ) =>
      r3StokesL2Operator hnu t.property f) := by
  have hfreq := continuous_r3StokesL2FrequencyMultiplier_orbit
    hnu (𝓕 f)
  have hout := (fourierInvCLM ℂ R3L2Velocity).continuous.comp hfreq
  change Continuous (fun t : Set.Ici (0 : ℝ) =>
    fourierInvCLM ℂ R3L2Velocity
      (r3StokesL2FrequencyMultiplier hnu t.property (𝓕 f)))
  exact hout

/-- The same-space Stokes evolution on stored order-three Bessel coordinates. -/
def r3StokesH3Operator
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 :=
  r3StokesL2Operator hnu ht

theorem r3StokesH3Operator_add_time
    {nu t s : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    r3StokesH3Operator hnu (add_nonneg ht hs) =
      (r3StokesH3Operator hnu ht).comp
        (r3StokesH3Operator hnu hs) :=
  r3StokesL2Operator_add_time hnu ht hs

theorem continuous_r3StokesH3Operator_orbit
    {nu : ℝ} (hnu : 0 ≤ nu) (f : R3HsVelocity 3) :
    Continuous (fun t : Set.Ici (0 : ℝ) =>
      r3StokesH3Operator hnu t.property f) :=
  continuous_r3StokesL2Operator_orbit hnu f

theorem continuous_r3StokesL2Operator_action
    {nu : ℝ} (hnu : 0 ≤ nu) :
    Continuous (fun p : Set.Ici (0 : ℝ) × R3L2Velocity =>
      r3StokesL2Operator hnu p.1.property p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hdelta : Tendsto
      (fun q : Set.Ici (0 : ℝ) × R3L2Velocity => q.2 - p.2)
      (𝓝 p) (𝓝 0) := by
    have hd := continuous_snd.continuousAt.sub
      (continuousAt_const : ContinuousAt
        (fun _ : Set.Ici (0 : ℝ) × R3L2Velocity => p.2) p)
    change Tendsto
      (fun q : Set.Ici (0 : ℝ) × R3L2Velocity => q.2 - p.2)
      (𝓝 p) (𝓝 (p.2 - p.2)) at hd
    simpa using hd
  have hdelta_norm : Tendsto
      (fun q : Set.Ici (0 : ℝ) × R3L2Velocity => ‖q.2 - p.2‖)
      (𝓝 p) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hdelta
  have hsmall_norm : Tendsto
      (fun q : Set.Ici (0 : ℝ) × R3L2Velocity =>
        ‖r3StokesL2Operator hnu q.1.property (q.2 - p.2)‖)
      (𝓝 p) (𝓝 0) :=
    squeeze_zero
      (fun _ => norm_nonneg _)
      (fun q => norm_r3StokesL2Operator_apply_le
        hnu q.1.property (q.2 - p.2))
      hdelta_norm
  have hsmall : Tendsto
      (fun q : Set.Ici (0 : ℝ) × R3L2Velocity =>
        r3StokesL2Operator hnu q.1.property (q.2 - p.2))
      (𝓝 p) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hsmall_norm
  have horbit : Tendsto
      (fun q : Set.Ici (0 : ℝ) × R3L2Velocity =>
        r3StokesL2Operator hnu q.1.property p.2)
      (𝓝 p) (𝓝 (r3StokesL2Operator hnu p.1.property p.2)) :=
    ((continuous_r3StokesL2Operator_orbit hnu p.2).comp
      continuous_fst).continuousAt
  have hsum := hsmall.add horbit
  change Tendsto
    (fun q : Set.Ici (0 : ℝ) × R3L2Velocity =>
      r3StokesL2Operator hnu q.1.property q.2)
    (𝓝 p) (𝓝 (r3StokesL2Operator hnu p.1.property p.2))
  simpa only [← map_add, sub_add_cancel, zero_add] using hsum

theorem continuous_r3StokesH3Operator_action
    {nu : ℝ} (hnu : 0 ≤ nu) :
    Continuous (fun p : Set.Ici (0 : ℝ) × R3HsVelocity 3 =>
      r3StokesH3Operator hnu p.1.property p.2) :=
  continuous_r3StokesL2Operator_action hnu

def r3NNRealToNonnegativeReal (t : ℝ≥0) : Set.Ici (0 : ℝ) :=
  ⟨(t : ℝ), t.property⟩

theorem continuous_r3NNRealToNonnegativeReal :
    Continuous r3NNRealToNonnegativeReal := by
  unfold r3NNRealToNonnegativeReal
  fun_prop

/-- Same-space order-three Stokes evolution indexed by elapsed nonnegative time. -/
def r3StokesH3Evolution
    {nu : ℝ} (hnu : 0 ≤ nu) (t : ℝ≥0) :
    R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 :=
  r3StokesH3Operator hnu t.property

theorem r3StokesH3Evolution_zero
    {nu : ℝ} (hnu : 0 ≤ nu) :
    r3StokesH3Evolution hnu 0 =
      ContinuousLinearMap.id ℂ (R3HsVelocity 3) :=
  r3StokesL2Operator_zero_time hnu

theorem r3StokesH3Evolution_add
    {nu : ℝ} (hnu : 0 ≤ nu) (t s : ℝ≥0) :
    r3StokesH3Evolution hnu (t + s) =
      (r3StokesH3Evolution hnu t).comp
        (r3StokesH3Evolution hnu s) :=
  r3StokesH3Operator_add_time hnu t.property s.property

theorem norm_r3StokesH3Evolution_apply_le
    {nu : ℝ} (hnu : 0 ≤ nu) (t : ℝ≥0) (f : R3HsVelocity 3) :
    ‖r3StokesH3Evolution hnu t f‖ ≤ ‖f‖ :=
  norm_r3StokesL2Operator_apply_le hnu t.property f

theorem norm_r3StokesH3Evolution_le_one
    {nu : ℝ} (hnu : 0 ≤ nu) (t : ℝ≥0) :
    ‖r3StokesH3Evolution hnu t‖ ≤ 1 :=
  (r3StokesH3Evolution hnu t).opNorm_le_bound zero_le_one
    (fun f => by
      simpa only [one_mul] using
        norm_r3StokesH3Evolution_apply_le hnu t f)

theorem continuous_r3StokesH3Evolution_orbit
    {nu : ℝ} (hnu : 0 ≤ nu) (f : R3HsVelocity 3) :
    Continuous (fun t : ℝ≥0 => r3StokesH3Evolution hnu t f) := by
  change Continuous
    ((fun t : Set.Ici (0 : ℝ) =>
      r3StokesH3Operator hnu t.property f) ∘
        r3NNRealToNonnegativeReal)
  exact (continuous_r3StokesH3Operator_orbit hnu f).comp
    continuous_r3NNRealToNonnegativeReal

theorem continuous_r3StokesH3Evolution_action
    {nu : ℝ} (hnu : 0 ≤ nu) :
    Continuous (fun p : ℝ≥0 × R3HsVelocity 3 =>
      r3StokesH3Evolution hnu p.1 p.2) := by
  have hpair : Continuous
      (fun p : ℝ≥0 × R3HsVelocity 3 =>
        (r3NNRealToNonnegativeReal p.1, p.2)) :=
    (continuous_r3NNRealToNonnegativeReal.comp continuous_fst).prodMk
      continuous_snd
  have h := (continuous_r3StokesH3Operator_action hnu).comp hpair
  change Continuous
    ((fun p : Set.Ici (0 : ℝ) × R3HsVelocity 3 =>
      r3StokesH3Operator hnu p.1.property p.2) ∘
        fun p : ℝ≥0 × R3HsVelocity 3 =>
          (r3NNRealToNonnegativeReal p.1, p.2))
  exact h

theorem r3H3InverseBesselL2FrequencyOperator_commutes_stokes
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) (g : R3L2Velocity) :
    r3H3InverseBesselL2FrequencyOperator
        (r3StokesL2FrequencyMultiplier hnu ht g) =
      r3StokesL2FrequencyMultiplier hnu ht
        (r3H3InverseBesselL2FrequencyOperator g) := by
  apply Lp.ext
  filter_upwards
    [r3H3InverseBesselL2FrequencyOperator_ae
      (r3StokesL2FrequencyMultiplier hnu ht g),
      r3StokesL2FrequencyMultiplier_ae hnu ht g,
      r3StokesL2FrequencyMultiplier_ae hnu ht
        (r3H3InverseBesselL2FrequencyOperator g),
      r3H3InverseBesselL2FrequencyOperator_ae g]
    with xi hleft hstokes hright hinverse
  rw [hleft, hstokes, hright, hinverse, smul_smul, smul_smul, mul_comm]

theorem r3H3ToL2Operator_r3StokesH3Evolution
    {nu : ℝ} (hnu : 0 ≤ nu) (t : ℝ≥0) (g : R3HsVelocity 3) :
    r3H3ToL2Operator (r3StokesH3Evolution hnu t g) =
      r3StokesL2Operator hnu t.property (r3H3ToL2Operator g) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change
    𝓕 (r3H3ToL2Operator (r3StokesL2Operator hnu t.property g)) =
      𝓕 (r3StokesL2Operator hnu t.property (r3H3ToL2Operator g))
  rw [fourier_r3H3ToL2Operator, fourier_r3StokesL2Operator,
    fourier_r3StokesL2Operator, fourier_r3H3ToL2Operator]
  exact r3H3InverseBesselL2FrequencyOperator_commutes_stokes
    hnu t.property (𝓕 g)

theorem r3StokesH2ToH3ScalarComplex_add_time
    (nu a b : ℝ) (xi : R3) :
    r3StokesH2ToH3ScalarComplex nu (a + b) xi =
      r3StokesScalarComplex nu b xi *
        r3StokesH2ToH3ScalarComplex nu a xi := by
  unfold r3StokesH2ToH3ScalarComplex
  rw [r3StokesScalarComplex_add_time]
  ring

theorem r3StokesH2ToH3FrequencyOperator_add_time
    {nu a b : ℝ} (hnu : 0 < nu) (ha : 0 < a) (hb : 0 ≤ b)
    (g : R3HsVelocity 2) :
    r3StokesH2ToH3FrequencyOperator hnu
        (add_pos_of_pos_of_nonneg ha hb) g =
      r3StokesL2FrequencyMultiplier hnu.le hb
        (r3StokesH2ToH3FrequencyOperator hnu ha g) := by
  apply Lp.ext
  filter_upwards
    [r3StokesH2ToH3FrequencyOperator_ae hnu
      (add_pos_of_pos_of_nonneg ha hb) g,
      r3StokesL2FrequencyMultiplier_ae hnu.le hb
        (r3StokesH2ToH3FrequencyOperator hnu ha g),
      r3StokesH2ToH3FrequencyOperator_ae hnu ha g]
    with xi hleft houter hinner
  rw [hleft, houter, hinner, smul_smul,
    r3StokesH2ToH3ScalarComplex_add_time]

theorem r3StokesH2ToH3Operator_add_time
    {nu a b : ℝ} (hnu : 0 < nu) (ha : 0 < a) (hb : 0 ≤ b) :
    r3StokesH2ToH3Operator hnu (add_pos_of_pos_of_nonneg ha hb) =
      (r3StokesH3Operator hnu.le hb).comp
        (r3StokesH2ToH3Operator hnu ha) := by
  apply ContinuousLinearMap.ext
  intro g
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change
    𝓕 (r3StokesH2ToH3Operator hnu
      (add_pos_of_pos_of_nonneg ha hb) g) =
      𝓕 (r3StokesL2Operator hnu.le hb
        (r3StokesH2ToH3Operator hnu ha g))
  rw [fourier_r3StokesH2ToH3Operator, fourier_r3StokesL2Operator,
    fourier_r3StokesH2ToH3Operator]
  exact r3StokesH2ToH3FrequencyOperator_add_time hnu ha hb (𝓕 g)

theorem r3StokesH2ToH3Operator_add_nnreal
    {nu a : ℝ} (hnu : 0 < nu) (ha : 0 < a) (b : ℝ≥0) :
    r3StokesH2ToH3Operator hnu
        (add_pos_of_pos_of_nonneg ha b.property) =
      (r3StokesH3Evolution hnu.le b).comp
        (r3StokesH2ToH3Operator hnu ha) :=
  r3StokesH2ToH3Operator_add_time hnu ha b.property

end

end MNS2
