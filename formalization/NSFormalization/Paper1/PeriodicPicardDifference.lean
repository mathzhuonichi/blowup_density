import NSFormalization.Paper1.PeriodicPicardBilinear

noncomputable section
namespace NSFormalization.Paper1.PeriodicPicardDifference

open NSFormalization.Paper1.PeriodicPicardBilinear

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

/-! Algebraic difference identities for the quadratic Fourier term.  These
identities are the first (purely finite-support) layer of a Picard contraction;
no norm, integration, or PDE existence assertion is made here. -/

theorem convolutionCoeff_self_sub_self_eq
    (u v : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff u u n - convolutionCoeff v v n =
      convolutionCoeff (u - v) u n + convolutionCoeff v (u - v) n := by
  have hu : (u - v) + v = u := sub_add_cancel u v
  have hleft : convolutionCoeff u u n =
      convolutionCoeff (u - v) u n + convolutionCoeff v u n := by
    rw [← hu, convolutionCoeff_add_left]
    simp [sub_add_cancel]
  have hright : convolutionCoeff v u n =
      convolutionCoeff v (u - v) n + convolutionCoeff v v n := by
    rw [← hu, convolutionCoeff_add_right]
    simp [sub_add_cancel]
  rw [hleft, hright]
  abel

theorem convolutionCoeff_quad_difference_eq
    (u v : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff u u n = convolutionCoeff v v n +
      convolutionCoeff (u - v) u n + convolutionCoeff v (u - v) n := by
  have h := convolutionCoeff_self_sub_self_eq u v n
  linear_combination h

end NSFormalization.Paper1.PeriodicPicardDifference
