import NSFormalization.Section4.B02.LowHigh
import NSFormalization.Section4.B02.Cutoff
import NSFormalization.Section4.D01.HomogeneousWitness

/-!
# B02, unit 6: the homogeneous datum of an `L¹ ∩ L²` field (`lebesgueHomogeneousDatum`)

This module discharges the field `lebesgueHomogeneousDatum` of
`research/B02/Spec.lean`'s `HomogeneousApproxAPI`
(`research/B02/Spec.lean:454`), the spatial realization of `Ḣ^s` used inside the
force-density argument `paper/sections/04-whole-space.tex:241-249`
(eq:homogeneous-realization, `02-preliminaries.tex:58-69`): for a **real** vector
field `k ∈ L¹ ∩ L²` and every order `-3/2 < s ≤ 0`,

* **existence**: `k` has an order-`s` homogeneous slice datum
  `G ∈ RealVectorSobolev s` (`Data.lean:367` `IsHomogeneousSliceDatum`), and
* **norm clause**: *every* datum of `k` has `ℝ≥0∞`-norm the Fourier quantity
  `Data.lean:410` `homogeneousFourierENorm s k`.

This is the first inhabitant of `Data.lean`'s homogeneous half at the
`L¹ ∩ L²` level (`research/I03/COMPARISON.md:284`, unit `U7c`'s spatial core):
`Section4/D01/HomogeneousWitness.lean` produced the datum only for *Schwartz* /
*compact-smooth* fields (`exists_isHomogeneousSliceDatum`,
`isHomogeneousSliceDatum_compact`), which do not cover the fields the diagonal
argument applies it to (`(1−χ_R)h_n`, Schwartz with unbounded support, and every
`k ∈ L¹ ∩ L²`).

## What is proved and how

The datum is `G_i := |ξ|^s · angularFourier k_i`, i.e. `D01`'s
`homogeneousProfile s k_i`, made an `L²` element:

* **finiteness** (`homogeneousProfile_memLp`): a genuinely new low/high split at
  angular radius `1`.  Low frequencies use the `L¹→L∞` sup bound
  `norm_angularFourier_le` (`‖k̂‖ ≤ (2π)^{-3/2}∫‖k‖`) together with
  `Section4/B02/LowFrequency.lean`'s `lowFrequencyIntegrable`
  (`∫_{|ξ|<1}|ξ|^{2s} < ∞` for `-3/2 < s`); high frequencies use `s ≤ 0`
  (`|ξ|^{2s} ≤ 1`) and lane 059's angular Plancherel
  `Section4/B02/LowHigh.lean` `angular_plancherel` (`∫|k̂|² = ‖k‖₂²`).  The
  Schwartz-only `SchwartzMap.integral_norm_sq_fourier` of the COMPARISON is
  *not* usable here; lane 059's `L¹ ∩ L²` Plancherel is.
* **membership in `realSubspace`** (`realSymmetry_lebesgueDatum`): the weight is
  real and even, so `RS:60` `fourier_conjugate` (via `D01`'s
  `angularFourier_conj_neg`) gives the conjugate-reflection symmetry — this is
  `04-whole-space.tex:249`'s "take real parts".
* **the realization identity** (`isHomogeneousSliceDatum_lebesgue`): the datum's
  distribution is the `L²` distribution of `k_i`, whose angular Fourier transform
  pairs against a Schwartz test as `∫ ψ · angularFourier k_i`
  (`angularFourierDistribution_lp_apply`, built over lane 059's `l2_fourier_pairing`
  and `AFD:98,172` `angularDistributionDilation`).
* **the norm clause** (`enorm_lebesgueVectorDatum` + `D01`'s
  `isHomogeneousSliceDatum_unique`, which holds at *every* real `s`): the
  constructed datum has norm `homogeneousFourierENorm s k` by `D01`'s
  `enorm_homogeneousDatum_sq`, and uniqueness pins every datum's norm.

## Reuse of `Section4/D01/HomogeneousWitness.lean`

The `D01.Homogeneous` machinery is reused *unchanged* — its
`homogeneousProfile`, `norm_homogeneousProfile_sq`, `angularFourier_conj_neg`,
`ae_ne_zero`, `enorm_sq_piLp`, `isHomogeneousSliceDatum_unique`,
`isHomogeneousVectorDatum_sub` and `isHomogeneousSliceDatum_sub`.  The `D01`
predicates `IsHomogeneousSliceDatum` etc. are *definitionally equal* to the
copies restated in `Section4/B02/Cutoff.lean` (lane 060), which this module opens
by being in the same namespace; the `D01` theorems apply to them by `rfl`.  What
is genuinely new relative to `D01` is the passage from Schwartz/compact fields to
`L¹ ∩ L²` fields, in `homogeneousProfile_memLp` and
`angularFourierDistribution_lp_apply`.

## The companion field `homogeneousDatumSub` is FALSE

`research/B02/Spec.lean:470` `homogeneousDatumSub` — that the datum of a
difference is the difference of the data, *with no integrability hypotheses* — is
**false** under `Data.lean:298`'s totalizing Bochner convention (lane 068 review,
`research/B02/REVIEW_U6.md` §4, machine-checked).  The witness for `z − w` is
forced (by injectivity of `angularFourierDistribution`) to be `U − V`, so
`IsSliceDistribution (z − w) (U − V)` reduces — provably an *iff* — to
`∫ ψ z_i − ∫ ψ w_i = ∫ ψ (z_i − w_i)`, i.e. additivity of the *physical* Bochner
pairing (`integral_sub`).  But a field pairing non-integrably with every Schwartz
test totalizes all its pairings to `0`, hence satisfies `IsSliceDistribution z 0`
vacuously and carries the *zero* homogeneous datum at every order.  A pair `z`,
`w` of such wild fields whose difference pairs non-trivially refutes the field:
with
`f = Σ_n 2^{-n} |x−q_n|^{-3} · 1_{0<|x−q_n|<2^{-n}}` over an enumeration `{q_n}`
of `ℚ³` (a.e. finite by Borel–Cantelli, yet `∫_B f = ∞` on every ball, so
`∫ ψ · f` totalizes to `0` for every Schwartz `ψ`) and `c` a nonzero real
Schwartz function, `z := (f,0,0)` and `w := (f − c,0,0)` both carry `Z = W = 0`,
while `z − w = (c,0,0)` has `∫ c·c > 0` — a nonzero datum.  No temperate-growth
development can prove the field: the existence of the distribution `U` does **not**
force `z` to have a locally integrable representative, precisely because
`IsSliceDistribution` totalizes.

The honest, fully-proved statement is `D01.Homogeneous.isHomogeneousSliceDatum_sub`,
which carries the two physical-pairing integrability side conditions; it is
re-exposed here as `isHomogeneousSliceDatum_sub_of_integrable`.  Those side
conditions are `Integrable.mul_bdd` (bounded × integrable) — of which `D01`'s
`integrable_schwartz_mul_component` is only the special case for a `ℂ`-valued
Schwartz *family*, covering neither call-site field literally.  Lane 060's
`spatialApproxHomogeneous_of` has been rewired to take `hDatumSub` in this
integrability-carrying form, its side conditions discharged at the single call
site by `Cutoff.lean`'s `integrable_schwartzVector` /
`integrable_cutoffCompl_schwartzVector`; `spatialApproxHomogeneous_of_units` below
instantiates the diagonal, leaving only unit 2 (`annularSchwartz`) as a hypothesis.
-/

open MeasureTheory Set NavierStokes.ProblemStatement NSFormalization.Source NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01.Homogeneous
  (homogeneousProfile norm_homogeneousProfile_sq angularFourier_conj_neg ae_ne_zero
    enorm_sq_piLp isHomogeneousSliceDatum_unique isHomogeneousSliceDatum_sub)
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ContDiff ComplexConjugate

noncomputable section
namespace NSFormalization.Section4.B02

/-! ## 1. The angular transform of an `L¹ ∩ L²` field -/

/-- The unitary angular transform of an integrable field is continuous
(`04-whole-space.tex:70`); reused for measurability and the sup bound. -/
theorem angularFourier_continuous (g : Space → ℂ) (hg1 : Integrable g volume) :
    Continuous (fun ξ => angularFourier g ξ) := by
  have h1 : Continuous (fun ξ : Space => 𝓕 g (frequencyUnit⁻¹ • ξ)) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ Space) continuous_inner hg1).comp (continuous_const_smul (frequencyUnit⁻¹))
  have h2 : Continuous
      (fun ξ : Space => frequencyUnit ^ (-3 / 2 : ℝ) • 𝓕 g (frequencyUnit⁻¹ • ξ)) :=
    h1.const_smul (frequencyUnit ^ (-3 / 2 : ℝ))
  simpa only [angularFourier] using h2

/-- The `L¹ → L∞` bound for the unitary angular transform: `‖k̂(ξ)‖ ≤ (2π)^{-3/2}∫‖k‖`
(`04-whole-space.tex:246`, `01-introduction.tex:91`).  Scalar form, holding at
every frequency; used at the low frequencies of `homogeneousProfile_memLp`. -/
theorem norm_angularFourier_le (g : Space → ℂ) (ξ : Space) :
    ‖angularFourier g ξ‖ ≤ frequencyUnit ^ (-3 / 2 : ℝ) * ∫ x, ‖g x‖ := by
  unfold angularFourier
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _)]
  exact mul_le_mul_of_nonneg_left
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)
    (Real.rpow_nonneg frequencyUnit_pos.le _)

/-- `02-preliminaries.tex:58-69` eq:homogeneous-realization at the `L¹ ∩ L²`
level: the angular-Fourier transform of the `L²` distribution of `g` pairs with a
Schwartz test exactly as `∫ ψ · angularFourier g`.  This is the multiplication
formula that `D01.Homogeneous.angularFourierDistribution_schwartz_apply` provides
for Schwartz `g`; here it is transported to every `g ∈ L¹ ∩ L²` over lane 059's
`l2_fourier_pairing` and `AFD:98` `angularDistributionDilation_apply` with the
`(2π)`-dilation change of variables. -/
theorem angularFourierDistribution_lp_apply (g : Space → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) (ψ : SchwartzMap Space ℂ) :
    angularFourierDistribution ((hg2.toLp g : Lp ℂ 2 (volume : Measure Space)) : 𝓢'(Space, ℂ)) ψ
      = ∫ ξ, ψ ξ • angularFourier g ξ := by
  set F : 𝓢'(Space, ℂ) := ((hg2.toLp g : Lp ℂ 2 (volume : Measure Space)) : 𝓢'(Space, ℂ)) with hF
  set c : ℝ := frequencyUnit with hc
  have hcpos : 0 < c := frequencyUnit_pos
  have hstep : angularFourierDistribution F ψ
      = c ^ (3 / 2 : ℝ) •
        ((𝓕 F) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale ψ)) := by
    change angularDistributionDilation (𝓕 F) ψ = _
    rw [angularDistributionDilation_apply]
  rw [hstep, Lp.fourier_toTemperedDistribution_eq (hg2.toLp g),
    l2_fourier_pairing g hg1 hg2
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale ψ)]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  have hCoV : (∫ ξ : Space, ψ (angularFrequencyScale ξ) • 𝓕 g ξ)
      = |(c ^ (Module.finrank ℝ Space))⁻¹| • ∫ η : Space, ψ η • 𝓕 g (c⁻¹ • η) := by
    have hcs := Measure.integral_comp_smul (volume : Measure Space)
        (fun η : Space => ψ η • 𝓕 g (c⁻¹ • η)) c
    rw [← hcs]
    apply integral_congr_ae; filter_upwards [] with ξ
    have hAS : angularFrequencyScale ξ = c • ξ := rfl
    rw [hAS, inv_smul_smul₀ hcpos.ne']
  rw [hCoV, finrank_space_eq_three, smul_smul]
  have hcoef : c ^ (3 / 2 : ℝ) * |(c ^ (3 : ℕ))⁻¹| = c ^ (-3 / 2 : ℝ) := by
    rw [abs_of_nonneg (inv_nonneg.mpr (by positivity)), ← Real.rpow_natCast c 3,
      ← Real.rpow_neg hcpos.le, ← Real.rpow_add hcpos]
    norm_num
  rw [hcoef, ← integral_smul]
  apply integral_congr_ae; filter_upwards [] with η
  rw [smul_comm]; rfl

/-! ## 2. Square-integrability of the homogeneous profile (the low/high split) -/

/-- `04-whole-space.tex:241-249`, the finiteness half of eq:Rnegative-cutoff at
the single-component level: for `g ∈ L¹ ∩ L²` and `-3/2 < s ≤ 0`, the homogeneous
profile `|ξ|^s ĝ` is square-integrable.  Low frequencies are controlled by the
`L¹→L∞` bound and `lowFrequencyIntegrable`; high frequencies by `|ξ|^{2s} ≤ 1`
and lane 059's `angular_plancherel`. -/
theorem homogeneousProfile_memLp {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Space → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    MemLp (homogeneousProfile s g) 2 volume := by
  have hcont := angularFourier_continuous g hg1
  have haesm : AEStronglyMeasurable (homogeneousProfile s g) volume := by
    unfold homogeneousProfile
    exact ((Complex.measurable_ofReal.comp (measurable_norm.pow_const s)).aestronglyMeasurable).mul
      hcont.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm haesm).mpr ?_
  have hrw : (fun ξ : Space => ‖homogeneousProfile s g ξ‖ ^ 2)
      = fun ξ => ‖ξ‖ ^ (2 * s) * ‖angularFourier g ξ‖ ^ 2 :=
    funext (norm_homogeneousProfile_sq s g)
  rw [hrw]
  have hmeas : Measurable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖angularFourier g ξ‖ ^ 2) :=
    (((by measurability : Measurable fun r : ℝ => r ^ (2 * s))).comp measurable_norm).mul
      (hcont.norm.measurable.pow_const 2)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have henorm : (fun ξ : Space => ‖‖ξ‖ ^ (2 * s) * ‖angularFourier g ξ‖ ^ 2‖ₑ)
      = fun ξ => ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖angularFourier g ξ‖ ^ 2) := by
    funext ξ; rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
  rw [henorm, ← lintegral_add_compl _ measurableSet_ball]
  apply ENNReal.add_lt_top.mpr
  refine ⟨?_, ?_⟩
  · -- Low frequencies: bounded transform against the integrable weight `|ξ|^{2s}`.
    set C₀ : ℝ := frequencyUnit ^ (-3 / 2 : ℝ) * ∫ x, ‖g x‖ with hC0
    have hbd : ∀ ξ, ‖angularFourier g ξ‖ ^ 2 ≤ C₀ ^ 2 := by
      intro ξ
      have h := norm_angularFourier_le g ξ
      have hC0nn : 0 ≤ C₀ := by
        rw [hC0]
        exact mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _)
          (integral_nonneg (fun x => norm_nonneg _))
      nlinarith [norm_nonneg (angularFourier g ξ)]
    have hstep1 : (∫⁻ ξ in Metric.ball (0 : Space) 1,
          ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖angularFourier g ξ‖ ^ 2))
        ≤ ∫⁻ ξ in Metric.ball (0 : Space) 1,
            ENNReal.ofReal (C₀ ^ 2) * ENNReal.ofReal (‖ξ‖ ^ (2 * s)) := by
      apply lintegral_mono; intro ξ
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C₀ ^ 2)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hbd ξ, Real.rpow_nonneg (norm_nonneg ξ) (2 * s)]
    refine lt_of_le_of_lt hstep1 ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (lowFrequencyIntegrable s hs)
        (ae_of_all _ (fun ξ => Real.rpow_nonneg (norm_nonneg _) _))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · -- High frequencies: `|ξ|^{2s} ≤ 1` and angular Plancherel.
    have hstep1 : (∫⁻ ξ in (Metric.ball (0 : Space) 1)ᶜ,
          ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖angularFourier g ξ‖ ^ 2))
        ≤ ∫⁻ ξ in (Metric.ball (0 : Space) 1)ᶜ, ENNReal.ofReal (‖angularFourier g ξ‖ ^ 2) := by
      apply setLIntegral_mono_ae' measurableSet_ball.compl
      filter_upwards [] with ξ hξ
      apply ENNReal.ofReal_le_ofReal
      have h1 : (1 : ℝ) ≤ ‖ξ‖ := by
        simpa [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hξ
      nlinarith [Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith : 2 * s ≤ 0),
        norm_nonneg (angularFourier g ξ), sq_nonneg (‖angularFourier g ξ‖)]
    refine lt_of_le_of_lt (le_trans hstep1 (setLIntegral_le_lintegral _ _)) ?_
    have hpl : (∫⁻ ξ, ENNReal.ofReal (‖angularFourier g ξ‖ ^ 2))
        = eLpNorm g 2 volume ^ (2 : ℝ) := by
      have he : (fun ξ : Space => ENNReal.ofReal (‖angularFourier g ξ‖ ^ 2))
          = fun ξ => ‖angularFourier g ξ‖ₑ ^ (2 : ℝ) := by
        funext ξ
        rw [← ofReal_norm (angularFourier g ξ), ENNReal.rpow_two,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [he, angular_plancherel g hg1 hg2, sq_eLpNorm_two]
    rw [hpl]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simpa using (hg2.eLpNorm_lt_top).ne)

/-! ## 3. The datum of a single `L¹ ∩ L²` field -/

/-- The `L²` datum `|ξ|^s ĝ` of an `L¹ ∩ L²` scalar field, the `L¹ ∩ L²`
counterpart of `D01.Homogeneous.homogeneousDatum`. -/
def lebesgueDatum {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Space → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) : FourierData :=
  (homogeneousProfile_memLp hs hs0 g hg1 hg2).toLp (homogeneousProfile s g)

theorem lebesgueDatum_ae {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Space → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    (lebesgueDatum hs hs0 g hg1 hg2 : Space → ℂ) =ᵐ[volume] homogeneousProfile s g :=
  MemLp.coeFn_toLp _

/-- `04-whole-space.tex:249` "take real parts": the datum of a real field lies in
the conjugate-reflection subspace `RS:118` `realSubspace`. -/
theorem realSymmetry_lebesgueDatum {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Space → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume)
    (hre : ∀ x, conj (g x) = g x) :
    realSymmetry (lebesgueDatum hs hs0 g hg1 hg2) = lebesgueDatum hs hs0 g hg1 hg2 := by
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (lebesgueDatum_ae hs hs0 g hg1 hg2)
  filter_upwards [realSymmetry_ae (lebesgueDatum hs hs0 g hg1 hg2),
    lebesgueDatum_ae hs hs0 g hg1 hg2, hneg] with ξ h1 h2 h3
  rw [h1, h3, h2]
  unfold homogeneousProfile
  rw [map_mul, Complex.conj_ofReal, norm_neg]
  exact congrArg _ (angularFourier_conj_neg hre ξ)

theorem mem_realSubspace_lebesgueDatum {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Space → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume)
    (hre : ∀ x, conj (g x) = g x) : lebesgueDatum hs hs0 g hg1 hg2 ∈ realSubspace s :=
  (mem_realSubspace_iff s _).mpr (realSymmetry_lebesgueDatum hs hs0 g hg1 hg2 hre)

/-- The datum's `L²` norm squared is the manuscript's literal Fourier quantity
(`Data.lean:410`, single component), the `L¹ ∩ L²` counterpart of `D01`'s
`enorm_homogeneousDatum_sq`. -/
theorem enorm_lebesgueDatum_sq {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Space → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    ‖lebesgueDatum hs hs0 g hg1 hg2‖ₑ ^ (2 : ℝ) =
      ∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖angularFourier g ξ‖ ^ 2) := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [ENNReal.rpow_inv_rpow (by norm_num : (2 : ℝ) ≠ 0)]
  apply lintegral_congr_ae
  filter_upwards [lebesgueDatum_ae hs hs0 g hg1 hg2] with ξ hξ
  rw [hξ, ← norm_homogeneousProfile_sq s g ξ, ← ofReal_norm,
    ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Removing the homogeneous weight recovers the angular transform, a.e. -/
theorem lebesgueDatum_weight_ae {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Space → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (lebesgueDatum hs hs0 g hg1 hg2 : Space → ℂ) ξ)
      =ᵐ[volume] fun ξ => angularFourier g ξ := by
  filter_upwards [lebesgueDatum_ae hs hs0 g hg1 hg2, ae_ne_zero] with ξ hξ hne
  have hpos : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hne
  have hone : (‖ξ‖ ^ (-s)) * (‖ξ‖ ^ s) = 1 := by rw [← Real.rpow_add hpos]; simp
  rw [hξ]
  unfold homogeneousProfile
  rw [← mul_assoc, ← Complex.ofReal_mul, hone]
  simp

/-! ## 4. The vector datum, its realization, and its norm -/

/-- The real three-vector homogeneous datum of an `L¹ ∩ L²` family, the
`L¹ ∩ L²` counterpart of `D01.Homogeneous.homogeneousVectorDatum`. -/
def lebesgueVectorDatum {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Fin 3 → Space → ℂ) (hg1 : ∀ i, Integrable (g i) volume)
    (hg2 : ∀ i, MemLp (g i) 2 volume) (hre : ∀ i x, conj (g i x) = g i x) :
    RealVectorSobolev s :=
  WithLp.toLp 2 fun i => ⟨lebesgueDatum hs hs0 (g i) (hg1 i) (hg2 i),
    mem_realSubspace_lebesgueDatum hs hs0 (g i) (hg1 i) (hg2 i) (hre i)⟩

@[simp] theorem lebesgueVectorDatum_coe {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (g : Fin 3 → Space → ℂ) (hg1 : ∀ i, Integrable (g i) volume)
    (hg2 : ∀ i, MemLp (g i) 2 volume) (hre : ∀ i x, conj (g i x) = g i x) (i : Fin 3) :
    ((lebesgueVectorDatum hs hs0 g hg1 hg2 hre i : RealSobolevHilbert s) : FourierData)
      = lebesgueDatum hs hs0 (g i) (hg1 i) (hg2 i) := rfl

/-- `04-whole-space.tex:226` prop:Renergy, the existence half at the spatial level
for an `L¹ ∩ L²` field: the physical slice `z` (with `L¹ ∩ L²` components `g`) has
the order-`s` homogeneous slice datum `lebesgueVectorDatum`.  This is the first
inhabitant of `Data.lean:367` `IsHomogeneousSliceDatum` outside the
Schwartz/compact classes of `D01`. -/
theorem isHomogeneousSliceDatum_lebesgue {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (z : Space → Space) (g : Fin 3 → Space → ℂ) (hg1 : ∀ i, Integrable (g i) volume)
    (hg2 : ∀ i, MemLp (g i) 2 volume) (hre : ∀ i x, conj (g i x) = g i x)
    (hz : ∀ i x, g i x = ((z x i : ℝ) : ℂ)) :
    IsHomogeneousSliceDatum s z (lebesgueVectorDatum hs hs0 g hg1 hg2 hre) := by
  refine ⟨fun i => ((hg2 i).toLp (g i) : 𝓢'(Space, ℂ)), ?_, ?_⟩
  · intro i χ
    show ((hg2 i).toLp (g i) : 𝓢'(Space, ℂ)) χ = _
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [(hg2 i).coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, hz i x]
  · intro i
    rw [lebesgueVectorDatum_coe]
    intro φ
    have hcancel : (fun ξ : Space =>
          φ ξ *
            (((‖ξ‖ ^ (-s) : ℝ) : ℂ) *
              (lebesgueDatum hs hs0 (g i) (hg1 i) (hg2 i) : Space → ℂ) ξ))
        =ᵐ[volume] fun ξ => φ ξ * angularFourier (g i) ξ := by
      filter_upwards [lebesgueDatum_weight_ae hs hs0 (g i) (hg1 i) (hg2 i)] with ξ hξ
      rw [hξ]
    refine ⟨?_, ?_⟩
    · exact (φ.integrable.mul_bdd
        (angularFourier_continuous (g i) (hg1 i)).aestronglyMeasurable
        (ae_of_all _ (fun ξ => norm_angularFourier_le (g i) ξ))).congr hcancel.symm
    · rw [angularFourierDistribution_lp_apply (g i) (hg1 i) (hg2 i) φ, integral_congr_ae hcancel]
      simp only [smul_eq_mul]

/-- The datum's norm is the manuscript's Fourier quantity `Data.lean:410`
`homogeneousFourierENorm`, the `L¹ ∩ L²` counterpart of `D01`'s
`enorm_homogeneousVectorDatum`. -/
theorem enorm_lebesgueVectorDatum {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (z : Space → Space) (g : Fin 3 → Space → ℂ) (hg1 : ∀ i, Integrable (g i) volume)
    (hg2 : ∀ i, MemLp (g i) 2 volume) (hre : ∀ i x, conj (g i x) = g i x)
    (hz : ∀ i x, g i x = ((z x i : ℝ) : ℂ)) :
    ‖lebesgueVectorDatum hs hs0 g hg1 hg2 hre‖ₑ = homogeneousFourierENorm s z := by
  have hcomp : ∀ i, (fun x : Space => ((z x i : ℝ) : ℂ)) = g i :=
    fun i => funext fun x => (hz i x).symm
  have hsq : ‖lebesgueVectorDatum hs hs0 g hg1 hg2 hre‖ₑ ^ (2 : ℝ) =
      ∑ i : Fin 3, ∫⁻ ξ : Space,
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖angularFourier (fun x => ((z x i : ℝ) : ℂ)) ξ‖ ^ 2) := by
    rw [enorm_sq_piLp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomp i]
    exact enorm_lebesgueDatum_sq hs hs0 (g i) (hg1 i) (hg2 i)
  rw [homogeneousFourierENorm, ← hsq, ENNReal.rpow_rpow_inv (by norm_num : (2 : ℝ) ≠ 0)]

/-! ## 5. The spec field `lebesgueHomogeneousDatum` -/

/-- `research/B02/Spec.lean:454` `lebesgueHomogeneousDatum`, both clauses.  For a
real `k ∈ L¹ ∩ L²` and `-3/2 < s ≤ 0`:

* **existence** — `k` has an order-`s` homogeneous slice datum, and
* **norm clause** — every datum of `k` has `ℝ≥0∞`-norm the Fourier quantity
  `homogeneousFourierENorm s k`.

The norm clause holds for *every* datum by `D01`'s uniqueness lemma
`isHomogeneousSliceDatum_unique` (valid at every real `s`); the constructed datum
`lebesgueVectorDatum` realizes it with the correct norm. -/
theorem lebesgueHomogeneousDatum {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    (k : Space → Space) (hk1 : MemLp k 1 volume) (hk2 : MemLp k 2 volume) :
    (∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G) ∧
      ∀ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G →
        ‖G‖ₑ = homogeneousFourierENorm s k := by
  set g : Fin 3 → Space → ℂ := fun i x => ((k x i : ℝ) : ℂ) with hg
  have hg_aesm : ∀ i, AEStronglyMeasurable (g i) volume := fun i =>
    (Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous).comp_aestronglyMeasurable
      hk2.aestronglyMeasurable
  have hg_le : ∀ i, ∀ x, ‖g i x‖ ≤ ‖k x‖ := by
    intro i x
    have hxeq : ‖g i x‖ = ‖k x i‖ := by simp [hg, Complex.norm_real]
    rw [hxeq]; exact PiLp.norm_apply_le (k x) i
  have hg1 : ∀ i, Integrable (g i) volume := fun i =>
    memLp_one_iff_integrable.mp (hk1.of_le (hg_aesm i) (ae_of_all _ (hg_le i)))
  have hg2 : ∀ i, MemLp (g i) 2 volume := fun i =>
    hk2.of_le (hg_aesm i) (ae_of_all _ (hg_le i))
  have hre : ∀ i x, conj (g i x) = g i x := fun i x => Complex.conj_ofReal _
  have hz : ∀ i x, g i x = ((k x i : ℝ) : ℂ) := fun _ _ => rfl
  have hbase := isHomogeneousSliceDatum_lebesgue hs hs0 k g hg1 hg2 hre hz
  refine ⟨⟨lebesgueVectorDatum hs hs0 g hg1 hg2 hre, hbase⟩, ?_⟩
  intro G hG
  rw [isHomogeneousSliceDatum_unique hG hbase]
  exact enorm_lebesgueVectorDatum hs hs0 k g hg1 hg2 hre hz

/-! ## 6. The companion field `homogeneousDatumSub` (integrability-carrying form)

The spec field `research/B02/Spec.lean:470` `homogeneousDatumSub` has no
integrability hypotheses and is **false** (see the module docstring and
`research/B02/ATTEMPTS_U6.md` §3 for the counterexample).  The honest,
fully-proved form is `D01`'s `isHomogeneousSliceDatum_sub`, re-exposed here in the
`B02` namespace and shape.  Its two side conditions are the *physical* pairing
integrability of `z` and `w`; they are `Integrable.mul_bdd` facts, supplied for
lane 060's diagonal by `Cutoff.lean`'s `integrable_schwartzVector` /
`integrable_cutoffCompl_schwartzVector`. -/
theorem isHomogeneousSliceDatum_sub_of_integrable {s : ℝ} {z w : Space → Space}
    {Z W : RealVectorSobolev s}
    (hZ : IsHomogeneousSliceDatum s z Z) (hW : IsHomogeneousSliceDatum s w W)
    (hz : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) volume)
    (hw : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ)) volume) :
    IsHomogeneousSliceDatum s (z - w) (Z - W) :=
  isHomogeneousSliceDatum_sub hZ hW hz hw

/-! ## 7. Discharging units 6, 7 and the sub-field of `spatialApproxHomogeneous_of`

Lane 060's `spatialApproxHomogeneous_of` (`Section4/B02/Cutoff.lean`) is stated
conditional on the unit-2, unit-6, sub-field and unit-7 hypotheses.  Its unit-6
hypothesis is exactly `lebesgueHomogeneousDatum` above, and its unit-7 hypothesis
is exactly lane 059's `lowHighSplit` (`Section4/B02/LowHigh.lean`); both are
discharged here, verbatim in the shape `spatialApproxHomogeneous_of` expects.  The
sub-field is discharged by `isHomogeneousSliceDatum_sub_of_integrable` (the
`hDatumSub` hypothesis of `spatialApproxHomogeneous_of` having been rewired to the
integrability-carrying form).  `spatialApproxHomogeneous_of_units` then leaves only
unit 2 (`annularSchwartz`) as a hypothesis of the stage-4 diagonal. -/
example : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
    MemLp k 1 volume → MemLp k 2 volume →
      (∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G) ∧
        ∀ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G →
          ‖G‖ₑ = homogeneousFourierENorm s k :=
  fun _s hs k hk1 hk2 => lebesgueHomogeneousDatum hs.1 hs.2 k hk1 hk2

example : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
    MemLp k 1 volume → MemLp k 2 volume →
      homogeneousFourierENorm s k ^ (2 : ℝ) ≤
        ENNReal.ofReal (lowHighConstant s) * eLpNorm k 1 volume ^ (2 : ℝ) +
          eLpNorm k 2 volume ^ (2 : ℝ) :=
  fun s hs k hk1 hk2 => lowHighSplit s hs.1 hs.2 k hk1 hk2

/-- The stage-4 diagonal density `04-whole-space.tex:249`, with units 6 and 7
supplied by this lane (`lebesgueHomogeneousDatum`, lane 059's `lowHighSplit`) and
the difference-of-data field by `isHomogeneousSliceDatum_sub_of_integrable`.  Only
unit 2 (`annularSchwartz`) remains as a hypothesis: `spatialApproxHomogeneous_of`
with three of its four hypotheses discharged. -/
theorem spatialApproxHomogeneous_of_units
    (hAnnularSchwartz : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
        ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
      ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W) :
    ∀ s : ℝ, SplitRange s → ∀ (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
      ∃ (h : SpatialField) (H : RealVectorSobolev s),
        ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsHomogeneousSliceDatum s h H ∧ ‖H - A‖ₑ < η :=
  spatialApproxHomogeneous_of hAnnularSchwartz
    (fun _s hs k hk1 hk2 => lebesgueHomogeneousDatum hs.1 hs.2 k hk1 hk2)
    (fun _s _z _w _Z _W hZ hW hz hw => isHomogeneousSliceDatum_sub_of_integrable hZ hW hz hw)
    (fun s hs k hk1 hk2 => lowHighSplit s hs.1 hs.2 k hk1 hk2)

end NSFormalization.Section4.B02
