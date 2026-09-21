import NSFormalization.Paper3.SobolevDensity

/-!
# Real Sobolev data inside the complete complex Fourier model

Reality is the conjugate-reflection symmetry of the weighted Fourier datum.
The underlying L2 quotients, reflection isometry and conjugation operator are
Mathlib constructions. The real-part projection will transfer physical complex
approximation to real-valued forces without changing their support.
-/
noncomputable section
namespace NSFormalization.Source.RealSobolev
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open scoped ContDiff ENNReal ComplexConjugate SchwartzMap Topology

abbrev FourierData := Lp ℂ 2 (volume : Measure Space)

def reflection : FourierData →ₗᵢ[ℝ] FourierData :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : Space => -ξ) (Measure.measurePreserving_neg volume)

def conjugation : FourierData →L[ℝ] FourierData :=
  Complex.conjLIE.toContinuousLinearMap.compLpL 2 volume

def realSymmetry : FourierData →L[ℝ] FourierData :=
  conjugation.comp reflection.toContinuousLinearMap

theorem realSymmetry_ae (h : FourierData) :
    (realSymmetry h : Space → ℂ) =ᵐ[volume] (fun ξ => conj (h (-ξ))) := by
  have hc := ContinuousLinearMap.coeFn_compLpL Complex.conjLIE.toContinuousLinearMap (reflection h)
  have hr := Lp.coeFn_compMeasurePreserving h (Measure.measurePreserving_neg volume)
  filter_upwards [hc, hr] with ξ hξ hrξ
  exact hξ.trans (congrArg conj hrξ)

theorem realSymmetry_involutive (h : FourierData) : realSymmetry (realSymmetry h) = h := by
  apply Lp.ext
  have hr := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (realSymmetry_ae h)
  filter_upwards [realSymmetry_ae (realSymmetry h), hr] with ξ hξ hrξ
  simp only [hξ, hrξ, neg_neg, starRingEnd_self_apply]

theorem realSymmetry_norm_le (h : FourierData) : ‖realSymmetry h‖ ≤ ‖h‖ := by
  have hc : ‖conjugation‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro z
      change ‖conj z‖ ≤ 1 * ‖z‖
      simp)
  exact (conjugation.le_opNorm (reflection h)).trans (by
    rw [reflection.norm_map]
    nlinarith [norm_nonneg h])

def conjugateSchwartz : SchwartzMap Space ℂ →L[ℝ] SchwartzMap Space ℂ :=
  SchwartzMap.postcompCLM Complex.conjLIE.toContinuousLinearMap

theorem conjugateSchwartz_apply (φ : SchwartzMap Space ℂ) (x : Space) :
    conjugateSchwartz φ x = conj (φ x) := rfl

/-- The actual Fourier integral intertwines physical conjugation with
conjugate reflection, in Mathlib's cycles-frequency convention. -/
theorem fourier_conjugate (f : Space → ℂ) (ξ : Space) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ)) := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [inner_neg_right, smul_eq_mul, map_mul, ← Complex.exp_conj,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

theorem weightedFourierLp_conjugate (s : ℝ) (φ : SchwartzMap Space ℂ) :
    weightedFourierLp s (conjugateSchwartz φ) = realSymmetry (weightedFourierLp s φ) := by
  apply Lp.ext
  have hr := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (weightedFourierLp_ae s φ)
  filter_upwards [weightedFourierLp_ae s (conjugateSchwartz φ),
    realSymmetry_ae (weightedFourierLp s φ), hr] with ξ hφ hJ hξ
  rw [hφ, hJ, hξ]
  change (1 + ‖ξ‖ ^ 2) ^ (s / 2) • 𝓕 (fun x => conj (φ x)) ξ = _
  rw [fourier_conjugate]
  simp only [norm_neg, Complex.real_smul, map_mul, Complex.conj_ofReal]

def realPartSchwartz : SchwartzMap Space ℂ →L[ℝ] SchwartzMap Space ℂ :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ + conjugateSchwartz)

theorem realPartSchwartz_apply (φ : SchwartzMap Space ℂ) (x : Space) :
    realPartSchwartz φ x = ((φ x).re : ℂ) := by
  change (1 / 2 : ℝ) • (φ x + conj (φ x)) = _
  apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im] <;> ring

def realProjection : FourierData →L[ℝ] FourierData :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ + realSymmetry)

theorem realProjection_apply (h : FourierData) :
    realProjection h = (1 / 2 : ℝ) • (h + realSymmetry h) := rfl

theorem weightedFourierLp_realPart (s : ℝ) (φ : SchwartzMap Space ℂ) :
    weightedFourierLp s (realPartSchwartz φ) = realProjection (weightedFourierLp s φ) := by
  change weightedFourierLp s ((1 / 2 : ℝ) • (φ + conjugateSchwartz φ)) = _
  rw [map_smul, map_add, weightedFourierLp_conjugate]
  rfl

theorem realProjection_symmetry (h : FourierData) :
    realSymmetry (realProjection h) = realProjection h := by
  rw [realProjection_apply, map_smul, map_add, realSymmetry_involutive]
  rw [add_comm]

theorem realProjection_norm_le (h : FourierData) : ‖realProjection h‖ ≤ ‖h‖ := by
  rw [realProjection_apply, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hn := (norm_add_le h (realSymmetry h)).trans
    (add_le_add le_rfl (realSymmetry_norm_le h))
  nlinarith

/-- The real Sobolev space is a closed real subspace of the complete weighted
Fourier Hilbert model. The parameter s determines its physical realization. -/
def realSubspace (_s : ℝ) : ClosedSubmodule ℝ FourierData :=
  (⊥ : ClosedSubmodule ℝ FourierData).comap (realSymmetry - ContinuousLinearMap.id ℝ FourierData)

abbrev RealSobolevHilbert (s : ℝ) := realSubspace s

theorem mem_realSubspace_iff (s : ℝ) (h : FourierData) :
    h ∈ realSubspace s ↔ realSymmetry h = h := by
  change realSymmetry h - h = 0 ↔ realSymmetry h = h
  exact sub_eq_zero

theorem realProjection_mem (s : ℝ) (h : FourierData) : realProjection h ∈ realSubspace s :=
  (mem_realSubspace_iff s _).mpr (realProjection_symmetry h)

theorem realProjection_eq_self {s : ℝ} {h : FourierData} (hh : h ∈ realSubspace s) :
    realProjection h = h := by
  rw [realProjection_apply, (mem_realSubspace_iff s h).mp hh, ← two_smul ℝ]
  simp [smul_smul]

end NSFormalization.Source.RealSobolev
