import NSFormalization.Section3.T20.CriticalEnergy

/-!
# T20 unit U5 — constant transport commutes with `Lambda`

This module proves the reconciled
`CriticalRegularityTAPI.constantTransportCommutesLambda` field verbatim.  For a
fixed spatial vector `m`, constant transport has Fourier symbol
`sum_j m_j (2 pi i k_j)`.  The periodic Lambda operator has the scalar symbol
`sqrt (4 pi^2 |k|^2)`, so the two multipliers commute coefficientwise.

The physical output is again smooth and periodic because `(m · nabla)z` is the
finite coordinate sum `sum_j m_j partial_j z`.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness (sum_coordinates)
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.A05 (dirDeriv)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff BigOperators

/-- Constant transport is the coordinate sum of the directional partials. -/
private theorem constantTransportSpatialT_eq_sum (m : Space) (z : SpatialField) (x : Space) :
    constantTransportSpatialT m z x = ∑ j : Fin 3, m j • dirDeriv j z x := by
  have hdir : constantTransportSpatialT m z x = fderiv ℝ z x m := rfl
  rw [hdir]
  conv_lhs => rw [← sum_coordinates m]
  simp only [map_sum, map_smul]
  rfl

/-- A fixed constant transport preserves smooth spatial periodicity. -/
private theorem smoothPeriodicT_constantTransportSpatialT (m : Space) {z : SpatialField}
    (hz : SmoothPeriodicT z) : SmoothPeriodicT (constantTransportSpatialT m z) := by
  obtain ⟨hs, hp⟩ := hz
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ (fun x ↦ fderiv ℝ z x m)
    exact (hs.fderiv_right (by simp)).clm_apply contDiff_const
  · intro x l
    rw [constantTransportSpatialT_eq_sum, constantTransportSpatialT_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [isPeriodicSpatial_dirDeriv hp j x l]

/-- `03-torus.tex:411`: a fixed constant-coefficient transport commutes with
the periodic Fourier multiplier `Lambda`. -/
theorem constantTransportCommutesLambda :
    ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
      IsPeriodicLambda v Lv →
        IsPeriodicLambda (constantTransportSpatialT m v)
          (constantTransportSpatialT m Lv) := by
  intro m v Lv hv hLv
  refine ⟨smoothPeriodicT_constantTransportSpatialT m hLv.1, ?_⟩
  intro i k
  change periodicFourierCoeff
      (fun x ↦ (((fderiv ℝ Lv x m : Space) i : ℝ) : ℂ)) k =
    Real.sqrt (periodicAngularFrequencySq k) *
      periodicFourierCoeff
        (fun x ↦ (((fderiv ℝ v x m : Space) i : ℝ) : ℂ)) k
  rw [periodicFourierCoeff_fderiv_dir hLv.1.1 hLv.1.2 m i k,
    hLv.2 i k, periodicFourierCoeff_fderiv_dir hv.1 hv.2 m i k]
  ring

end NSFormalization.Section3.T20
