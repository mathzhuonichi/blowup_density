import NSFormalization.Paper3.RealVectorPositiveDensity
import NSFormalization.Source.RealSobolev
import NavierStokes.R3.ComparisonCutoffs
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# B02 unit 1: annular truncation of a homogeneous datum

This module proves the two spec fields `annularRestriction` and `annularSmoothing`
of `research/B02/Spec.lean` (`BlowupDensity.B02.Draft.HomogeneousApproxAPI`,
fields at `Spec.lean:302-318`), which formalise the first stage of the
manuscript's homogeneous `Ḣ^{-1}` approximation, `paper/sections/04-whole-space.tex:241`:

> "One first restricts to `1/n < |ξ| < n`, with `L²` error tending to zero, and
> then smooths each restricted function with a sufficiently small mollification
> radius and a slightly larger annular cutoff."

A datum of `RealVectorSobolev s` is an element of the reality (conjugate-reflection)
subspace of a weighted `L²` on the Fourier side (`Paper3/RealVectorPositiveDensity.lean:15`,
`Source/RealSobolev.lean`); the datum norm `‖·‖ₑ` read below is literally the
`L²(ℝ³;ℂ³)` norm of that Fourier-side representative.  We show:

* `annularRestriction` — every datum is approximated in the datum norm by its
  restriction to a compact frequency annulus `δ ≤ ‖ξ‖ ≤ R` away from the origin
  (`0 < δ`), the `L²` error tending to zero by dominated convergence, the
  truncation staying in the reality subspace because the annulus is `ξ ↦ -ξ`
  invariant and its indicator real (`Source.RealSobolev.realSymmetry_ae`);
* `annularSmoothing` — a datum supported (a.e.) in the open annulus `δ < ‖ξ‖ < R`
  is approximated in the datum norm by a smooth one, compactly supported in a
  slightly larger closed annulus `δ' ≤ ‖ξ‖ ≤ R'` (`0 < δ' < δ`, `R < R'`), still
  in the reality subspace, using Mathlib's smooth-compact `Lᵖ` density
  (`MeasureTheory.MemLp.exist_eLpNorm_sub_le`), a real annular cutoff built from
  the fixed bump `NavierStokesR3.ComparisonCutoffs.cutoff`, and the reality
  projection `Paper3.realProjectionTo`.

## §0.  The spec predicates, restated

`NSFormalization` is a dependency of the `Contracts` library and cannot import
`Contracts.V1.Data`, where the specification lives.  The five predicates below are
restated **token-for-token** from `research/B02/Spec.lean:155-192` (their bodies
are copied verbatim, only the namespace differs), so that the theorems proved here
are definitionally the two spec fields; the conformance file
`research/B02/axioms_u1.lean` discharges the spec-typed obligations with them.
-/

noncomputable section

namespace NSFormalization.Section4.B02

open MeasureTheory Filter
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NavierStokes.ProblemStatement (Space)
open NavierStokesR3.ComparisonCutoffs
open scoped ENNReal ContDiff ComplexConjugate Topology


/-- `research/B02/Spec.lean:155`.  The open frequency annulus `δ < ‖ξ‖ < R`. -/
def frequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ < ‖ξ‖ ∧ ‖ξ‖ < R}

/-- `research/B02/Spec.lean:161`.  The closed frequency annulus `δ ≤ ‖ξ‖ ≤ R`. -/
def closedFrequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R}

/-- `research/B02/Spec.lean:172`.  `Z` is an order-`s` datum whose three components
are (a.e.) smooth functions supported in the closed annulus `δ ≤ ‖ξ‖ ≤ R`. -/
def IsAnnularDatum {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∃ g : Fin 3 → Space → ℂ,
    (∀ i, ContDiff ℝ ∞ (g i)) ∧
    (∀ i, tsupport (g i) ⊆ closedFrequencyAnnulus δ R) ∧
    (∀ i, ((Z i : FourierData) : Space → ℂ) =ᵐ[volume] g i)

/-- `research/B02/Spec.lean:181`.  `Z` is the restriction of `A` to the open
annulus `δ < ‖ξ‖ < R`. -/
def IsAnnularRestriction {s : ℝ} (δ R : ℝ) (A Z : RealVectorSobolev s) : Prop :=
  ∀ i, ((Z i : FourierData) : Space → ℂ)
    =ᵐ[volume] (frequencyAnnulus δ R).indicator ((A i : FourierData) : Space → ℂ)

/-- `research/B02/Spec.lean:190`.  The datum of `Z` vanishes a.e. off the open
annulus `δ < ‖ξ‖ < R`. -/
def IsAnnularSupported {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∀ i : Fin 3, ∀ᵐ ξ : Space ∂volume,
    ξ ∉ frequencyAnnulus δ R → ((Z i : FourierData) : Space → ℂ) ξ = 0

/-! ## §1.  Elementary facts about the annulus and the datum norm -/

/-- The open frequency annulus is measurable. -/
theorem measurableSet_frequencyAnnulus (δ R : ℝ) : MeasurableSet (frequencyAnnulus δ R) :=
  (measurableSet_lt measurable_const continuous_norm.measurable).inter
    (measurableSet_lt continuous_norm.measurable measurable_const)

/-- The closed frequency annulus is closed. -/
theorem isClosed_closedFrequencyAnnulus (δ R : ℝ) : IsClosed (closedFrequencyAnnulus δ R) :=
  (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

/-- The open frequency annulus is invariant under `ξ ↦ -ξ` (its two constraints only
see `‖ξ‖`). -/
theorem neg_mem_frequencyAnnulus (δ R : ℝ) (ξ : Space) :
    -ξ ∈ frequencyAnnulus δ R ↔ ξ ∈ frequencyAnnulus δ R := by
  show (δ < ‖-ξ‖ ∧ ‖-ξ‖ < R) ↔ (δ < ‖ξ‖ ∧ ‖ξ‖ < R)
  rw [norm_neg]

/-- The datum norm is dominated by the sum of the three component norms, so
per-component estimates give a bound on `‖X - Y‖ₑ`. -/
theorem enorm_sub_lt_of_forall_le {s : ℝ} (X Y : RealVectorSobolev s) {ε : ℝ} (hε : 0 < ε)
    (hb : ∀ i, ‖(X - Y) i‖ ≤ ε / 4) : ‖X - Y‖ₑ < ENNReal.ofReal ε := by
  have hnn : ∀ i, (0 : ℝ) ≤ ‖(X - Y) i‖ := fun i => norm_nonneg _
  have hsum_le : ∑ i, ‖(X - Y) i‖ ≤ 3 * (ε / 4) := by
    rw [Fin.sum_univ_three]
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; linarith
  have hsq : ∑ i, ‖(X - Y) i‖ ^ 2 ≤ (∑ i, ‖(X - Y) i‖) ^ 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    nlinarith [hnn 0, hnn 1, hnn 2]
  have hnorm : ‖X - Y‖ ≤ 3 * (ε / 4) := by
    rw [PiLp.norm_eq_of_L2]
    calc Real.sqrt (∑ i, ‖(X - Y) i‖ ^ 2)
        ≤ Real.sqrt ((∑ i, ‖(X - Y) i‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ∑ i, ‖(X - Y) i‖ := Real.sqrt_sq (Finset.sum_nonneg (fun i _ => hnn i))
      _ ≤ 3 * (ε / 4) := hsum_le
  calc ‖X - Y‖ₑ = ENNReal.ofReal ‖X - Y‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (3 * (ε / 4)) := ENNReal.ofReal_le_ofReal hnorm
    _ < ENNReal.ofReal ε := by rw [ENNReal.ofReal_lt_ofReal_iff hε]; linarith

/-- Choose a positive real cushion below a positive extended threshold. -/
theorem exists_real_le_enorm {η : ℝ≥0∞} (hη : 0 < η) : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ η := by
  rcases eq_or_ne η ⊤ with rfl | hη'
  · exact ⟨1, one_pos, le_top⟩
  · exact ⟨η.toReal, ENNReal.toReal_pos hη.ne' hη', (ENNReal.ofReal_toReal hη').le⟩

/-- The a.e. conjugate-reflection (Hermitian) symmetry of the Fourier-side
representative of an element of the reality subspace `realSubspace s`:
`(X ξ) = conj (X (-ξ))` a.e.  This is the `mem_realSubspace_iff`/`realSymmetry_ae`
step used to keep truncations and realized weights real; it is factored out here so
`annularTruncLp_mem` and `AnnularReal.angularFourier_realPart_ae` share the one copy. -/
theorem realSobolevHilbert_conj_reflection_ae {s : ℝ} (X : RealSobolevHilbert s) :
    ((X : FourierData) : Space → ℂ) =ᵐ[volume]
      fun ξ => conj (((X : FourierData) : Space → ℂ) (-ξ)) := by
  have hA : realSymmetry (X : FourierData) = (X : FourierData) :=
    (mem_realSubspace_iff s _).mp X.property
  have h1 : ((realSymmetry (X : FourierData) : Space → ℂ)) =ᵐ[volume]
      ((X : FourierData) : Space → ℂ) := by rw [hA]
  filter_upwards [realSymmetry_ae (X : FourierData), h1] with ξ e1 e2
  rw [← e2]; exact e1

/-! ## §2.  `annularRestriction`: truncation to a compact annulus -/

/-- The `L²` error of restricting a single Fourier-side function to the annulus
`(n+2)⁻¹ < ‖ξ‖ < n+2` tends to zero: dominated convergence for the tail
`∫_{annulusᶜ}‖f‖²`, which shrinks to the null set `{0}`. -/
theorem tendsto_eLpNorm_annulus_compl (f : Space → ℂ) (hf : MemLp f 2 volume) :
    Tendsto (fun n : ℕ =>
      eLpNorm ((frequencyAnnulus ((n : ℝ) + 2)⁻¹ ((n : ℝ) + 2))ᶜ.indicator f) 2 volume)
      atTop (𝓝 0) := by
  have hfae : AEMeasurable f volume := hf.aestronglyMeasurable.aemeasurable
  have hmeas_h : AEMeasurable (fun ξ => ‖f ξ‖ₑ ^ (2 : ℝ)) volume := hfae.enorm.pow_const 2
  have h_fin : ∫⁻ ξ, ‖f ξ‖ₑ ^ (2 : ℝ) ∂volume ≠ ⊤ := by
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := volume) (f := f) (p := 2)
      (by norm_num) (by norm_num)).1 hf.2
    simpa using this.ne
  set S : ℕ → Set Space := fun n => frequencyAnnulus ((n : ℝ) + 2)⁻¹ ((n : ℝ) + 2) with hS
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => measurableSet_frequencyAnnulus _ _
  have hlim : Tendsto (fun n : ℕ => ∫⁻ ξ in (S n)ᶜ, ‖f ξ‖ₑ ^ (2 : ℝ) ∂volume) atTop (𝓝 0) := by
    have hne : ∀ᵐ ξ : Space ∂volume, ξ ≠ (0 : Space) :=
      (ae_iff).mpr (by simp only [ne_eq, not_not]; exact measure_singleton (0 : Space))
    have key := tendsto_lintegral_of_dominated_convergence'
      (μ := volume) (F := fun n => (S n)ᶜ.indicator (fun ξ => ‖f ξ‖ₑ ^ (2 : ℝ)))
      (f := fun _ => (0 : ℝ≥0∞))
      (fun ξ => ‖f ξ‖ₑ ^ (2 : ℝ))
      (fun n => hmeas_h.indicator (hSmeas n).compl)
      (fun n => ae_of_all _ (fun ξ => Set.indicator_le_self _ _ ξ))
      h_fin
      (by
        filter_upwards [hne] with ξ hξ
        have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
        have hev : ∀ᶠ n : ℕ in atTop,
            (S n)ᶜ.indicator (fun ξ => ‖f ξ‖ₑ ^ (2 : ℝ)) ξ = 0 := by
          have e1 : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 2)⁻¹ < ‖ξ‖ :=
            (tendsto_atTop_add_const_right atTop 2
              tendsto_natCast_atTop_atTop).inv_tendsto_atTop.eventually_lt_const hpos
          have e2 : ∀ᶠ n : ℕ in atTop, ‖ξ‖ < (n : ℝ) + 2 :=
            (tendsto_atTop_add_const_right atTop 2
              tendsto_natCast_atTop_atTop).eventually_gt_atTop ‖ξ‖
          filter_upwards [e1, e2] with n hn1 hn2
          have hmemS : ξ ∈ S n := ⟨hn1, hn2⟩
          rw [Set.indicator_of_notMem (not_not.mpr hmemS)]
        exact tendsto_const_nhds.congr' (by filter_upwards [hev] with n hn; exact hn.symm))
    have hrw : ∀ n : ℕ, ∫⁻ ξ, (S n)ᶜ.indicator (fun ξ => ‖f ξ‖ₑ ^ (2 : ℝ)) ξ ∂volume
        = ∫⁻ ξ in (S n)ᶜ, ‖f ξ‖ₑ ^ (2 : ℝ) ∂volume :=
      fun n => lintegral_indicator (hSmeas n).compl _
    simpa only [hrw, lintegral_zero] using key
  have heq : ∀ n : ℕ,
      eLpNorm ((S n)ᶜ.indicator f) 2 volume
        = (∫⁻ ξ in (S n)ᶜ, ‖f ξ‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hSmeas n).compl,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  rw [tendsto_congr heq]
  have := hlim.ennrpow_const (1 / (2 : ℝ))
  simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this

/-- The Fourier-side annular restriction of a real datum component, as an `L²`
class. -/
def annularTruncLp {s : ℝ} (δ R : ℝ) (A : RealSobolevHilbert s) : FourierData :=
  ((Lp.memLp (A : FourierData)).indicator (measurableSet_frequencyAnnulus δ R)).toLp

/-- The annular restriction agrees a.e. with the indicator (on the open annulus) of
the datum component's Fourier-side representative. -/
theorem annularTruncLp_ae {s : ℝ} (δ R : ℝ) (A : RealSobolevHilbert s) :
    (annularTruncLp δ R A : Space → ℂ) =ᵐ[volume]
      (frequencyAnnulus δ R).indicator ((A : FourierData) : Space → ℂ) :=
  MemLp.coeFn_toLp _

/-- The annular restriction stays in the reality subspace: the annulus is
`ξ ↦ -ξ` invariant and its indicator real, so it commutes with `realSymmetry`. -/
theorem annularTruncLp_mem {s : ℝ} (δ R : ℝ) (A : RealSobolevHilbert s) :
    annularTruncLp δ R A ∈ realSubspace s := by
  rw [mem_realSubspace_iff]
  apply Lp.ext
  have hSym := realSobolevHilbert_conj_reflection_ae A
  have hI := annularTruncLp_ae δ R A
  have hIneg := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae hI
  filter_upwards [realSymmetry_ae (annularTruncLp δ R A), hI, hIneg, hSym]
    with ξ hs hi hin hsy
  rw [hs, hin, hi]
  by_cases hmem : ξ ∈ frequencyAnnulus δ R
  · have hnegmem : -ξ ∈ frequencyAnnulus δ R := (neg_mem_frequencyAnnulus δ R ξ).mpr hmem
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hnegmem]
    exact hsy.symm
  · have hnegmem : -ξ ∉ frequencyAnnulus δ R :=
      fun h => hmem ((neg_mem_frequencyAnnulus δ R ξ).mp h)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hnegmem, map_zero]

/-- `research/B02/Spec.lean:302-304` `annularRestriction`, `04-whole-space.tex:241`
("One first restricts to `1/n < |ξ| < n`, with `L²` error tending to zero"): every
order-`s` datum `A` is approximated in the datum norm by its restriction `Z` to a
compact frequency annulus `0 < δ ≤ ‖ξ‖ ≤ R` away from the origin, `Z` still in the
reality subspace. -/
theorem annularRestriction (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ (δ R : ℝ) (Z : RealVectorSobolev s),
      0 < δ ∧ δ < R ∧ IsAnnularRestriction δ R A Z ∧ ‖Z - A‖ₑ < η := by
  obtain ⟨ε, hε, hεη⟩ := exists_real_le_enorm hη
  have hev : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 3,
      eLpNorm ((frequencyAnnulus ((n : ℝ) + 2)⁻¹ ((n : ℝ) + 2))ᶜ.indicator
        ((A i : FourierData) : Space → ℂ)) 2 volume < ENNReal.ofReal (ε / 4) := by
    refine Filter.eventually_all.mpr (fun i => ?_)
    exact (tendsto_eLpNorm_annulus_compl _ (Lp.memLp (A i : FourierData))).eventually
      (isOpen_Iio.mem_nhds (by simpa using ENNReal.ofReal_pos.mpr (by positivity)))
  obtain ⟨n, hn⟩ := hev.exists
  set R₀ : ℝ := (n : ℝ) + 2 with hR₀
  set δ₀ : ℝ := R₀⁻¹ with hδ₀
  have hR₀pos : 0 < R₀ := by rw [hR₀]; positivity
  set Zc : Fin 3 → RealSobolevHilbert s :=
    fun i => ⟨annularTruncLp δ₀ R₀ (A i), annularTruncLp_mem δ₀ R₀ (A i)⟩ with hZc
  refine ⟨δ₀, R₀, WithLp.toLp 2 Zc, by rw [hδ₀]; positivity, ?_, ?_, ?_⟩
  · have hone : (1 : ℝ) < R₀ := by rw [hR₀]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hinv : δ₀ ≤ 1 := by rw [hδ₀]; exact inv_le_one_of_one_le₀ hone.le
    linarith
  · intro i
    show ⇑(annularTruncLp δ₀ R₀ (A i)) =ᵐ[volume]
      (frequencyAnnulus δ₀ R₀).indicator ((A i : FourierData) : Space → ℂ)
    exact annularTruncLp_ae δ₀ R₀ (A i)
  · refine lt_of_lt_of_le (enorm_sub_lt_of_forall_le _ _ hε (fun i => ?_)) hεη
    have hcomp : (WithLp.toLp 2 Zc - A) i = Zc i - A i := rfl
    rw [hcomp]
    have heLp : eLpNorm (annularTruncLp δ₀ R₀ (A i) - (A i : FourierData)) 2 volume
        = eLpNorm ((frequencyAnnulus δ₀ R₀)ᶜ.indicator
            ((A i : FourierData) : Space → ℂ)) 2 volume := by
      have hae : ⇑(annularTruncLp δ₀ R₀ (A i) - (A i : FourierData)) =ᵐ[volume]
          -((frequencyAnnulus δ₀ R₀)ᶜ.indicator ((A i : FourierData) : Space → ℂ)) := by
        filter_upwards [Lp.coeFn_sub (annularTruncLp δ₀ R₀ (A i)) (A i : FourierData),
          annularTruncLp_ae δ₀ R₀ (A i)] with ξ hsub htr
        rw [hsub, Pi.sub_apply, htr, Pi.neg_apply]
        by_cases hx : ξ ∈ frequencyAnnulus δ₀ R₀
        · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx)]; ring
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx)]; ring
      rw [eLpNorm_congr_ae hae, eLpNorm_neg]
    have hnormeq : ‖Zc i - A i‖
        = (eLpNorm ((frequencyAnnulus δ₀ R₀)ᶜ.indicator
            ((A i : FourierData) : Space → ℂ)) 2 volume).toReal := by
      rw [show ‖Zc i - A i‖ = ‖annularTruncLp δ₀ R₀ (A i) - (A i : FourierData)‖ from rfl,
        Lp.norm_def, heLp]
    rw [hnormeq]
    have hfin : eLpNorm ((frequencyAnnulus δ₀ R₀)ᶜ.indicator
        ((A i : FourierData) : Space → ℂ)) 2 volume ≠ ⊤ :=
      ne_top_of_le_ne_top (Lp.memLp (A i : FourierData)).2.ne (eLpNorm_indicator_le _)
    have hle := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr (hn i).le
    rwa [ENNReal.toReal_ofReal (by positivity)] at hle

/-! ## §3.  `annularSmoothing`: smoothing inside a slightly larger annulus -/

/-- A smooth real cutoff equal to `1` on the closed annulus `δ ≤ ‖ξ‖ ≤ R` and
supported in the open annulus `δ/2 < ‖ξ‖ < 2R`, built from the fixed bump. -/
def annularCutoff (δ R : ℝ) (ξ : Space) : ℝ := cutoff R ξ * (1 - cutoff (δ / 2) ξ)

/-- The annular cutoff is smooth (product of the two smooth bump factors). -/
theorem annularCutoff_smooth (δ R : ℝ) : ContDiff ℝ ∞ (annularCutoff δ R) :=
  (cutoff_smooth R).mul (contDiff_const.sub (cutoff_smooth (δ / 2)))

/-- The annular cutoff is nonnegative. -/
theorem annularCutoff_nonneg (δ R : ℝ) (ξ : Space) : 0 ≤ annularCutoff δ R ξ :=
  mul_nonneg (cutoff_nonneg R ξ) (by linarith [cutoff_le_one (δ / 2) ξ])

/-- The annular cutoff is bounded by `1`. -/
theorem annularCutoff_le_one (δ R : ℝ) (ξ : Space) : annularCutoff δ R ξ ≤ 1 :=
  mul_le_one₀ (cutoff_le_one R ξ) (by linarith [cutoff_le_one (δ / 2) ξ])
    (by linarith [cutoff_nonneg (δ / 2) ξ])

/-- The annular cutoff equals `1` on the closed annulus `δ ≤ ‖ξ‖ ≤ R`. -/
theorem annularCutoff_eq_one {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) {ξ : Space}
    (h : δ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R) : annularCutoff δ R ξ = 1 := by
  have h1 : cutoff R ξ = 1 := cutoff_eq_one hR h.2
  have h2 : cutoff (δ / 2) ξ = 0 := cutoff_eq_zero (by positivity) (by nlinarith [h.1])
  rw [annularCutoff, h1, h2]; ring

/-- The annular cutoff is supported in the open annulus `δ/2 < ‖ξ‖ < 2R`. -/
theorem annularCutoff_support {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) {ξ : Space}
    (h : annularCutoff δ R ξ ≠ 0) : δ / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2 * R := by
  rw [annularCutoff] at h
  have hc1 : cutoff R ξ ≠ 0 := fun hz => h (by rw [hz]; ring)
  have hc2 : (1 - cutoff (δ / 2) ξ) ≠ 0 := fun hz => h (by rw [hz]; ring)
  constructor
  · by_contra hle
    rw [not_lt] at hle
    exact hc2 (by rw [cutoff_eq_one (by positivity) hle]; ring)
  · by_contra hle
    rw [not_lt] at hle
    exact hc1 (cutoff_eq_zero hR hle)

/-- `research/B02/Spec.lean:314-318` `annularSmoothing`, `04-whole-space.tex:241`
("then smooths each restricted function with a sufficiently small mollification
radius and a slightly larger annular cutoff"): a datum `Z` supported a.e. in the
open annulus `δ < ‖ξ‖ < R` is approximated in the datum norm by a smooth one `W`,
compactly supported in a slightly larger closed annulus `δ' ≤ ‖ξ‖ ≤ R'`, still in
the reality subspace. -/
theorem annularSmoothing (s : ℝ) (δ R : ℝ) (hδ : 0 < δ) (hδR : δ < R)
    (Z : RealVectorSobolev s) (hZ : IsAnnularSupported δ R Z) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ (δ' R' : ℝ) (W : RealVectorSobolev s),
      0 < δ' ∧ δ' < δ ∧ R < R' ∧ IsAnnularDatum δ' R' W ∧ ‖W - Z‖ₑ < η := by
  have hR : 0 < R := hδ.trans hδR
  obtain ⟨ε, hε, hεη⟩ := exists_real_le_enorm hη
  choose g₀ hg₀c hg₀s hg₀e using fun i : Fin 3 =>
    MeasureTheory.MemLp.exist_eLpNorm_sub_le (μ := volume) (p := 2) (by norm_num) (by norm_num)
      (Lp.memLp (Z i : FourierData)) (show (0 : ℝ) < ε / 4 by positivity)
  set χ : Space → ℝ := annularCutoff δ R with hχ
  have hχsmooth : ContDiff ℝ ∞ χ := annularCutoff_smooth δ R
  have hχcompact : HasCompactSupport χ := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Space) (2 * R))
      (isClosed_tsupport χ)
    refine closure_minimal (fun ξ hξ => ?_) Metric.isClosed_closedBall
    have hs := annularCutoff_support hδ hR hξ
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [hs.2]
  set v : Fin 3 → Space → ℂ := fun i ξ => χ ξ • g₀ i ξ with hv
  set g : Fin 3 → Space → ℂ := fun i ξ => (1 / 2 : ℝ) • (v i ξ + conj (v i (-ξ))) with hg
  have hvsmooth : ∀ i, ContDiff ℝ ∞ (v i) := fun i => hχsmooth.smul (hg₀s i)
  have hvcompact : ∀ i, HasCompactSupport (v i) := fun i => hχcompact.smul_right
  have hvmem : ∀ i, MemLp (v i) 2 volume := fun i =>
    (hvsmooth i).continuous.memLp_of_hasCompactSupport (hvcompact i)
  set W : RealVectorSobolev s := WithLp.toLp 2 (fun i => realProjectionTo s (hvmem i).toLp) with hW
  refine ⟨δ / 2, 2 * R, W, by positivity, by linarith, by linarith, ?_, ?_⟩
  · refine ⟨g, fun i => ?_, fun i => ?_, fun i => ?_⟩
    · have h1 : ContDiff ℝ ∞ (fun ξ => conj (v i (-ξ))) :=
        Complex.conjCLE.contDiff.comp ((hvsmooth i).comp contDiff_neg)
      exact ((hvsmooth i).add h1).const_smul (1 / 2 : ℝ)
    · apply closure_minimal ?_ (isClosed_closedFrequencyAnnulus (δ / 2) (2 * R))
      intro ξ hξ
      have hgξ : g i ξ ≠ 0 := hξ
      have hsum : v i ξ + conj (v i (-ξ)) ≠ 0 := by
        intro hz; apply hgξ; rw [hg]; simp [hz]
      rcases (show v i ξ ≠ 0 ∨ conj (v i (-ξ)) ≠ 0 by
        by_contra hbc
        simp only [not_or, not_not] at hbc
        exact hsum (by rw [hbc.1, hbc.2]; ring)) with hne | hne
      · have hχne : χ ξ ≠ 0 := fun hz => hne (by rw [hv]; simp [hz])
        have hs := annularCutoff_support hδ hR hχne
        exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      · have hvne : v i (-ξ) ≠ 0 := fun hz => hne (by rw [hz]; simp)
        have hχne : χ (-ξ) ≠ 0 := fun hz => hvne (by rw [hv]; simp [hz])
        have hs := annularCutoff_support hδ hR hχne
        rw [norm_neg] at hs
        exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    · have hX : (((hvmem i).toLp : FourierData) : Space → ℂ) =ᵐ[volume] v i :=
        MemLp.coeFn_toLp _
      have hXneg := (Measure.measurePreserving_neg
        (volume : Measure Space)).quasiMeasurePreserving.ae hX
      have hrp : ((W i : FourierData) : Space → ℂ) =ᵐ[volume]
          fun ξ => (1 / 2 : ℝ) • ((((hvmem i).toLp : FourierData) : Space → ℂ) ξ
            + conj ((((hvmem i).toLp : FourierData) : Space → ℂ) (-ξ))) := by
        have hpr : (W i : FourierData) = realProjection ((hvmem i).toLp) := rfl
        rw [hpr, realProjection_apply]
        filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) ((hvmem i).toLp + realSymmetry (hvmem i).toLp),
          Lp.coeFn_add ((hvmem i).toLp) (realSymmetry (hvmem i).toLp),
          realSymmetry_ae ((hvmem i).toLp)] with ξ a1 a2 a3
        rw [a1, Pi.smul_apply, a2, Pi.add_apply, a3]
      filter_upwards [hrp, hX, hXneg] with ξ b1 b2 b3
      rw [b1]
      simp only [hg]
      rw [b2, b3]
  · refine lt_of_lt_of_le (enorm_sub_lt_of_forall_le _ _ hε (fun i => ?_)) hεη
    have hcomp : (W - Z) i = realProjectionTo s (hvmem i).toLp - Z i := rfl
    rw [hcomp]
    have hZrp : realProjectionTo s ((Z i : FourierData)) = Z i := realProjectionTo_inclusion s (Z i)
    rw [← hZrp, ← map_sub]
    refine le_trans (realProjectionTo_norm_le s _) ?_
    rw [Lp.norm_def]
    have hbound : eLpNorm ((hvmem i).toLp - (Z i : FourierData)) 2 volume
        ≤ ENNReal.ofReal (ε / 4) := by
      refine le_trans (eLpNorm_mono_ae ?_) (hg₀e i)
      filter_upwards [Lp.coeFn_sub ((hvmem i).toLp) (Z i : FourierData),
        MemLp.coeFn_toLp (hvmem i), hZ i] with ξ hsub hvl hZξ
      rw [hsub, Pi.sub_apply, hvl, Pi.sub_apply]
      by_cases hzero : ((Z i : FourierData) : Space → ℂ) ξ = 0
      · rw [hzero, sub_zero, zero_sub, norm_neg]
        simp only [hv, norm_smul]
        have hle : ‖χ ξ‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (annularCutoff_nonneg δ R ξ)]
          exact annularCutoff_le_one δ R ξ
        calc ‖χ ξ‖ * ‖g₀ i ξ‖ ≤ 1 * ‖g₀ i ξ‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
          _ = ‖g₀ i ξ‖ := one_mul _
      · have hmem : ξ ∈ frequencyAnnulus δ R := by
          by_contra hbc; exact hzero (hZξ hbc)
        have hχ1 : χ ξ = 1 := annularCutoff_eq_one hδ hR ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
        simp only [hv, hχ1, one_smul]
        exact le_of_eq (norm_sub_rev (g₀ i ξ) (((Z i : FourierData) : Space → ℂ) ξ))
    have hfin : eLpNorm ((hvmem i).toLp - (Z i : FourierData)) 2 volume ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
    calc (eLpNorm ((hvmem i).toLp - (Z i : FourierData)) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 4)).toReal :=
          (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hbound
      _ = ε / 4 := ENNReal.toReal_ofReal (by positivity)

end NSFormalization.Section4.B02
