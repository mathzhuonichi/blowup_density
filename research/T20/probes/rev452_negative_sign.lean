import NSFormalization.Section3.T20.TransportLambda

/-!
Reviewer mutation probe for lane 452.

The conclusion below changes the Lambda symbol from `+sqrt(4*pi^2*|k|^2)`
to its negative while retaining every binder and hypothesis.  Replaying the
delivered coefficient rewrites must therefore leave the false residual `A=-A`.
-/

noncomputable section

namespace NSFormalization.Section3.T20.Rev452NegativeSign

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open NSFormalization.Section3.T20

example :
    ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
      IsPeriodicLambda v Lv →
        SmoothPeriodicT (constantTransportSpatialT m Lv) ∧
          ∀ (i : Fin 3) (k : PeriodicFrequency),
            periodicFourierCoeff
                (fun x ↦ (((constantTransportSpatialT m Lv x) i : ℝ) : ℂ)) k =
              -(Real.sqrt (periodicAngularFrequencySq k) : ℂ) *
                periodicFourierCoeff
                  (fun x ↦ (((constantTransportSpatialT m v x) i : ℝ) : ℂ)) k := by
  intro m v Lv hv hLv
  have hOriginal := constantTransportCommutesLambda m v Lv hv hLv
  refine ⟨hOriginal.1, ?_⟩
  intro i k
  change periodicFourierCoeff
      (fun x ↦ (((fderiv ℝ Lv x m : Space) i : ℝ) : ℂ)) k =
    -(Real.sqrt (periodicAngularFrequencySq k) : ℂ) *
      periodicFourierCoeff
        (fun x ↦ (((fderiv ℝ v x m : Space) i : ℝ) : ℂ)) k
  rw [periodicFourierCoeff_fderiv_dir hLv.1.1 hLv.1.2 m i k,
    hLv.2 i k, periodicFourierCoeff_fderiv_dir hv.1 hv.2 m i k]
  ring

end NSFormalization.Section3.T20.Rev452NegativeSign
