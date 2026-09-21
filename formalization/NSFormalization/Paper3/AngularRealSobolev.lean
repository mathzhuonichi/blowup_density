import NSFormalization.Paper3.AngularSobolevClass

/-! Normalized angular transport on the existing complete real Sobolev subspace.
The underlying data norm is L2; physical realization changes with the order.
No new Fourier transform, completion, or physical reality predicate is introduced. -/
noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source RealSobolev
open scoped SchwartzMap ENNReal ComplexConjugate

/-- Conjugate reflection on Schwartz frequency data, using Mathlib composition. -/
def frequencyRealSchwartz (φ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  conjugateSchwartz (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := Space)) φ)

@[simp] theorem frequencyRealSchwartz_apply (φ : SchwartzMap Space ℂ) (ξ : Space) :
    frequencyRealSchwartz φ ξ = conj (φ (-ξ)) := rfl

theorem frequencyRealSchwartz_toLp (φ : SchwartzMap Space ℂ) :
    (frequencyRealSchwartz φ).toLp 2 volume = realSymmetry (φ.toLp 2 volume) := by
  apply Lp.ext
  have hr := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (φ.coeFn_toLp 2 volume)
  filter_upwards [(frequencyRealSchwartz φ).coeFn_toLp 2 volume,
    realSymmetry_ae (φ.toLp 2 volume), hr] with ξ hξ hJ hφ
  rw [hξ, hJ, hφ]
  rfl

/-- The real normalization amplitude and real frequency dilation commute
with actual conjugate reflection, first on the Schwartz core. -/
theorem schwartzAngularDilation_realSymmetry (φ : SchwartzMap Space ℂ) :
    schwartzAngularDilation (frequencyRealSchwartz φ) =
      frequencyRealSchwartz (schwartzAngularDilation φ) := by
  ext ξ
  simp only [schwartzAngularDilation_apply, frequencyRealSchwartz_apply,
    smul_neg, Complex.real_smul, map_mul, Complex.conj_ofReal]

/-- Preservation of reality for arbitrary L2 data follows by density. -/
theorem angularFrequencyDilation_realSymmetry (h : FourierData) :
    angularFrequencyDilation (realSymmetry h) =
      realSymmetry (angularFrequencyDilation h) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Space) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top).induction_on h
    (isClosed_eq (angularFrequencyDilation.continuous.comp realSymmetry.continuous)
      (realSymmetry.continuous.comp angularFrequencyDilation.continuous)) ?_
  intro φ
  change angularFrequencyDilation (realSymmetry (φ.toLp 2 volume)) =
    realSymmetry (angularFrequencyDilation (φ.toLp 2 volume))
  rw [← frequencyRealSchwartz_toLp, angularFrequencyDilation_toLp,
    angularFrequencyDilation_toLp, schwartzAngularDilation_realSymmetry,
    frequencyRealSchwartz_toLp]

theorem cyclesToAngular_realSymmetry (s : ℝ) (h : SobolevHilbert s) :
    realSymmetry (cyclesToAngular s h) = cyclesToAngular s (realSymmetry h) := by
  change realSymmetry (angularFrequencyDilation (angularWeightEquiv s h)) =
    angularFrequencyDilation (angularWeightEquiv s (realSymmetry h))
  rw [← angularFrequencyDilation_realSymmetry, angularWeightEquiv_realSymmetry]

theorem cyclesToAngular_mem_realSubspace (s : ℝ) (h : SobolevHilbert s) :
    cyclesToAngular s h ∈ realSubspace s ↔ h ∈ realSubspace s := by
  rw [mem_realSubspace_iff, mem_realSubspace_iff, cyclesToAngular_realSymmetry]
  exact (cyclesToAngular s).injective.eq_iff

/-- The complete real equivalence uses the normalized angular datum,
including frequency dilation, rather than only a change of Bessel weight. -/
def cyclesToAngularReal (s : ℝ) : RealSobolevHilbert s ≃L[ℝ] RealSobolevHilbert s :=
  ((cyclesToAngular s).restrictScalars ℝ).ofSubmodules
    (realSubspace s).toSubmodule (realSubspace s).toSubmodule (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (cyclesToAngular_mem_realSubspace s x).mpr hx
      · intro hy
        refine ⟨(cyclesToAngular s).symm y, ?_, (cyclesToAngular s).apply_symm_apply y⟩
        apply (cyclesToAngular_mem_realSubspace s _).mp
        change y ∈ realSubspace s at hy
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy)

theorem cyclesToAngularReal_norm_le (s : ℝ) (h : RealSobolevHilbert s) :
    ‖cyclesToAngularReal s h‖ ≤ frequencyUnit ^ |s| * ‖h‖ :=
  cyclesToAngular_norm_le s h

theorem cyclesToAngularReal_symm_norm_le (s : ℝ) (h : RealSobolevHilbert s) :
    ‖(cyclesToAngularReal s).symm h‖ ≤ frequencyUnit ^ |s| * ‖h‖ :=
  cyclesToAngular_symm_norm_le s h

/-- The same physical tempered distribution survives the real transport. -/
theorem angularRealization_cyclesToAngularReal (s : ℝ) (h : RealSobolevHilbert s) :
    angularRealization s (cyclesToAngularReal s h : FourierData) =
      sobolevRealization s (h : FourierData) :=
  angularRealization_cyclesToAngular s h

end NSFormalization.Paper3
