import NSFormalization.Paper1.PeriodicPicardDifference
import NSFormalization.Paper1.PeriodicFinitePicardCoeffBound

noncomputable section
namespace NSFormalization.Paper1.PeriodicPicardDifferenceBound

open NSFormalization.Paper1.PeriodicPicardBilinear
open NSFormalization.Paper1.PeriodicFinitePicardCoeffBound
open NSFormalization.Paper1.PeriodicPicardDifference

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

theorem norm_convolutionCoeff_quad_difference_le
    (u v : FiniteFourier) (n : PeriodicFrequency) :
    ‖convolutionCoeff u u n - convolutionCoeff v v n‖ ≤
      (∑ k ∈ (u - v).support.filter (fun k => u (n - k) ≠ 0),
        ‖(u - v) k‖ * ‖u (n - k)‖) +
      (∑ k ∈ v.support.filter (fun k => (u - v) (n - k) ≠ 0),
        ‖v k‖ * ‖(u - v) (n - k)‖) := by
  rw [convolutionCoeff_self_sub_self_eq]
  calc
    ‖convolutionCoeff (u - v) u n + convolutionCoeff v (u - v) n‖ ≤
        ‖convolutionCoeff (u - v) u n‖ + ‖convolutionCoeff v (u - v) n‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_convolutionCoeff_le _ _ _) (norm_convolutionCoeff_le _ _ _)

end NSFormalization.Paper1.PeriodicPicardDifferenceBound
