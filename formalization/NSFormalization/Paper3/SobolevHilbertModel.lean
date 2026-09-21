import NSFormalization.Paper3.WeightedFourierLp

/-!
# A complete Hilbert model for Sobolev distributions

Weighted Fourier data live in the genuine Hilbert space `Lp ℂ 2 volume`.
Their realization is inverse Fourier transform after multiplication by the
inverse Bessel weight, performed on tempered distributions. Thus non-L1
backgrounds are included; no pointwise Bochner Fourier integral is postulated.
The realization is injective and its range is exactly Mathlib `MemSobolev s 2`.
The Sobolev Hilbert norm is the data-space norm, not the weaker distribution
subspace topology.
-/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff ENNReal SchwartzMap

/-- The actual complete Hilbert data space for order `s`. The order determines
the realization, while its data norm is the usual complex L² norm. -/
abbrev SobolevHilbert (_s : ℝ) := Lp ℂ 2 (volume : Measure Space)

/-- Complex-valued Bessel weight used by distributional multiplication. -/
def sobolevBesselWeight (s : ℝ) (ξ : Space) : ℂ :=
  ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)

 theorem sobolevBesselWeight_temperate (s : ℝ) :
    (sobolevBesselWeight s).HasTemperateGrowth := by
  unfold sobolevBesselWeight
  fun_prop

 theorem sobolevBesselWeight_mul (s r : ℝ) :
    sobolevBesselWeight s * sobolevBesselWeight r = sobolevBesselWeight (s + r) := by
  funext ξ
  simp only [Pi.mul_apply, sobolevBesselWeight, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖ ^ 2)]
  congr 1
  ring

/-- Bessel multiplication on the actual space of tempered distributions. -/
def sobolevWeightMultiplier (s : ℝ) : 𝓢'(Space, ℂ) →L[ℂ] 𝓢'(Space, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ (sobolevBesselWeight s)

 theorem sobolevWeightMultiplier_add (s r : ℝ) (u : 𝓢'(Space, ℂ)) :
    sobolevWeightMultiplier r (sobolevWeightMultiplier s u) = sobolevWeightMultiplier (s + r) u := by
  unfold sobolevWeightMultiplier
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (sobolevBesselWeight_temperate s) (sobolevBesselWeight_temperate r), sobolevBesselWeight_mul]

@[simp] theorem sobolevWeightMultiplier_zero (u : 𝓢'(Space, ℂ)) :
    sobolevWeightMultiplier 0 u = u := by
  have hw : sobolevBesselWeight 0 = fun _ : Space => (1 : ℂ) := by
    funext ξ
    simp [sobolevBesselWeight]
  rw [sobolevWeightMultiplier, hw, TemperedDistribution.smulLeftCLM_const, one_smul]

/-- Distributional weighted Fourier transform. -/
def weightedFourierDistribution (s : ℝ) : 𝓢'(Space, ℂ) →L[ℂ] 𝓢'(Space, ℂ) :=
  (sobolevWeightMultiplier s).comp (fourierCLM ℂ 𝓢'(Space, ℂ))

/-- Distributional inverse to the weighted Fourier transform. -/
def sobolevReconstruction (s : ℝ) : 𝓢'(Space, ℂ) →L[ℂ] 𝓢'(Space, ℂ) :=
  (fourierInvCLM ℂ 𝓢'(Space, ℂ)).comp (sobolevWeightMultiplier (-s))

@[simp] theorem weightedFourier_reconstruction (s : ℝ) (u : 𝓢'(Space, ℂ)) :
    weightedFourierDistribution s (sobolevReconstruction s u) = u := by
  change sobolevWeightMultiplier s (𝓕 (𝓕⁻ (sobolevWeightMultiplier (-s) u))) = u
  rw [fourier_fourierInv_eq, sobolevWeightMultiplier_add, neg_add_cancel, sobolevWeightMultiplier_zero]

@[simp] theorem reconstruction_weightedFourier (s : ℝ) (u : 𝓢'(Space, ℂ)) :
    sobolevReconstruction s (weightedFourierDistribution s u) = u := by
  change 𝓕⁻ (sobolevWeightMultiplier (-s) (sobolevWeightMultiplier s (𝓕 u))) = u
  rw [sobolevWeightMultiplier_add, add_neg_cancel, sobolevWeightMultiplier_zero, fourierInv_fourier_eq]

/-- Actual realization of a Sobolev Hilbert datum as a tempered distribution. -/
def sobolevRealization (s : ℝ) : SobolevHilbert s →L[ℂ] 𝓢'(Space, ℂ) :=
  (sobolevReconstruction s).comp (Lp.toTemperedDistributionCLM ℂ volume 2)

@[simp] theorem sobolevRealization_apply (s : ℝ) (h : SobolevHilbert s) :
    sobolevRealization s h = sobolevReconstruction s (h : 𝓢'(Space, ℂ)) := rfl

/-- Applying the weighted Fourier transform recovers the original L² datum
as a distribution. No L1 assumption occurs. -/
@[simp] theorem weightedFourier_realization (s : ℝ) (h : SobolevHilbert s) :
    weightedFourierDistribution s (sobolevRealization s h) = (h : 𝓢'(Space, ℂ)) := by
  rw [sobolevRealization_apply, weightedFourier_reconstruction]

 theorem sobolevRealization_injective (s : ℝ) : Function.Injective (sobolevRealization s) := by
  intro h g heq
  have htd := congrArg (weightedFourierDistribution s) heq
  simp only [weightedFourier_realization] at htd
  have hi : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  exact hi htd

/-- Every Hilbert datum realizes an actual Mathlib Sobolev distribution. -/
theorem sobolevRealization_memSobolev (s : ℝ) (h : SobolevHilbert s) :
    TemperedDistribution.MemSobolev s 2 (sobolevRealization s h) := by
  apply TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mpr
  refine ⟨h, ?_⟩
  exact weightedFourier_realization s h

/-- Conversely every Mathlib Sobolev distribution has a Hilbert datum. -/
theorem mem_range_sobolevRealization_iff (s : ℝ) (u : 𝓢'(Space, ℂ)) :
    u ∈ Set.range (sobolevRealization s) ↔ TemperedDistribution.MemSobolev s 2 u := by
  constructor
  · rintro ⟨h, rfl⟩
    exact sobolevRealization_memSobolev s h
  · intro hu
    obtain ⟨h, hh⟩ := TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mp hu
    have hd : weightedFourierDistribution s u = (h : 𝓢'(Space, ℂ)) := hh
    refine ⟨h, ?_⟩
    rw [sobolevRealization_apply, ← hd, reconstruction_weightedFourier]

 theorem range_sobolevRealization (s : ℝ) :
    Set.range (sobolevRealization s) = {u : 𝓢'(Space, ℂ) | TemperedDistribution.MemSobolev s 2 u} := by
  ext u
  exact mem_range_sobolevRealization_iff s u

/-- The representation of every Sobolev distribution is unique. -/
theorem existsUnique_sobolev_datum {s : ℝ} {u : 𝓢'(Space, ℂ)}
    (hu : TemperedDistribution.MemSobolev s 2 u) :
    ∃! h : SobolevHilbert s, sobolevRealization s h = u := by
  obtain ⟨h, hh⟩ := (mem_range_sobolevRealization_iff s u).mpr hu
  exact ⟨h, hh, fun g hg => sobolevRealization_injective s (hg.trans hh.symm)⟩

/-- At order zero this is exactly the genuine L² inverse Fourier transform,
embedded in distributions. This covers L² functions without an L1 hypothesis. -/
theorem sobolevRealization_zero (h : SobolevHilbert 0) :
    sobolevRealization 0 h = ((𝓕⁻ h : Lp ℂ 2 (volume : Measure Space)) : 𝓢'(Space, ℂ)) := by
  change 𝓕⁻ (sobolevWeightMultiplier (-0) (h : 𝓢'(Space, ℂ))) = _
  rw [neg_zero, sobolevWeightMultiplier_zero]
  exact Lp.fourierInv_toTemperedDistribution_eq h

end NSFormalization.Paper3
