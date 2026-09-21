import NSFormalization.Paper3.AngularTameProduct

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped SchwartzMap ENNReal

/-- The actual distributional dilation is injective, because its test map
is the inverse of the checked Schwartz dilation equivalence. -/
theorem angularDistributionDilation_injective : Function.Injective angularDistributionDilation := by
  intro U V h
  ext ψ
  have H := congrArg (fun T : 𝓢'(Space, ℂ) => T (schwartzAngularDilation ψ)) h
  change U (schwartzAngularDilationInv (schwartzAngularDilation ψ)) =
    V (schwartzAngularDilationInv (schwartzAngularDilation ψ)) at H
  have hi : schwartzAngularDilationInv (schwartzAngularDilation ψ) = ψ :=
    schwartzAngularDilationEquiv.symm_apply_apply ψ
  rwa [hi] at H

/-- Fourier inversion and dilation injectivity identify the actual angular
Fourier transform faithfully on all tempered distributions. -/
theorem angularFourierDistribution_injective : Function.Injective angularFourierDistribution := by
  intro U V h
  change angularDistributionDilation (𝓕 U) = angularDistributionDilation (𝓕 V) at h
  have H := congrArg (fun T : 𝓢'(Space, ℂ) => 𝓕⁻ T)
    (angularDistributionDilation_injective h)
  simpa only [fourierInv_fourier_eq] using H

/-- Bessel multiplication is injective at every real order. -/
theorem sobolevWeightMultiplier_injective (s : ℝ) : Function.Injective (sobolevWeightMultiplier s) := by
  intro U V h
  have H := congrArg (sobolevWeightMultiplier (-s)) h
  simpa only [sobolevWeightMultiplier_add, add_neg_cancel, sobolevWeightMultiplier_zero] using H

theorem weightedAngularFourier_injective (s : ℝ) :
    Function.Injective (fun U : 𝓢'(Space, ℂ) => sobolevWeightMultiplier s (angularFourierDistribution U)) :=
  (sobolevWeightMultiplier_injective s).comp angularFourierDistribution_injective

/-- The actual complete angular class: its weighted angular Fourier
transform is represented by an L2 datum. No topology is assigned here. -/
def MemAngularSobolev (s : ℝ) (U : 𝓢'(Space, ℂ)) : Prop :=
  ∃ l : Lp ℂ 2 (volume : Measure Space),
    sobolevWeightMultiplier s (angularFourierDistribution U) = (l : 𝓢'(Space, ℂ))

/-- The checked right inverse is also a left reconstruction identity whenever
the actual weighted angular transform is represented by L2 data. -/
theorem angularRealization_eq_of_weightedAngularFourier_eq (s : ℝ) {U : 𝓢'(Space, ℂ)}
    {l : Lp ℂ 2 (volume : Measure Space)}
    (h : sobolevWeightMultiplier s (angularFourierDistribution U) = (l : 𝓢'(Space, ℂ))) :
    angularRealization s l = U :=
  weightedAngularFourier_injective s ((weightedAngularFourier_realization s l).trans h.symm)

/-- Exact complete range, in both directions, for the angular realization. -/
theorem mem_range_angularRealization_iff (s : ℝ) (U : 𝓢'(Space, ℂ)) :
    U ∈ Set.range (angularRealization s) ↔ MemAngularSobolev s U := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l, weightedAngularFourier_realization s l⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, angularRealization_eq_of_weightedAngularFourier_eq s hl⟩

theorem range_angularRealization_eq_class (s : ℝ) :
    Set.range (angularRealization s) = {U : 𝓢'(Space, ℂ) | MemAngularSobolev s U} := by
  ext U
  exact mem_range_angularRealization_iff s U

/-- The complete angular datum is unique, not merely a chosen representative. -/
theorem MemAngularSobolev.exists_unique_datum {s : ℝ} {U : 𝓢'(Space, ℂ)}
    (hU : MemAngularSobolev s U) :
    ∃! l : Lp ℂ 2 (volume : Measure Space),
      sobolevWeightMultiplier s (angularFourierDistribution U) = (l : 𝓢'(Space, ℂ)) := by
  obtain ⟨l, hl⟩ := hU
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply angularRealization_injective s
  exact (angularRealization_eq_of_weightedAngularFourier_eq s hk).trans
    (angularRealization_eq_of_weightedAngularFourier_eq s hl).symm

/-- The angular and cycles data realize exactly the same physical range. -/
theorem range_angularRealization_eq_cycles (s : ℝ) :
    Set.range (angularRealization s) = Set.range (sobolevRealization s) := by
  ext U
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨(cyclesToAngular s).symm l, (angularRealization_eq_cycles s l).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨cyclesToAngular s h, angularRealization_cyclesToAngular s h⟩

/-- Exact normalization-faithful class equality for arbitrary tempered
distributions; Sobolev norm topology remains on the complete L2 data. -/
theorem memAngularSobolev_iff_memSobolev (s : ℝ) (U : 𝓢'(Space, ℂ)) :
    MemAngularSobolev s U ↔ TemperedDistribution.MemSobolev s 2 U := by
  rw [← mem_range_angularRealization_iff, range_angularRealization_eq_cycles,
    mem_range_sobolevRealization_iff]

end NSFormalization.Paper3
