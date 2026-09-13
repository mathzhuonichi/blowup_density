import NSFormalization.Paper1.PeriodicPicardBilinear

noncomputable section
namespace NSFormalization.Paper1.PeriodicFinitePicardCoeffBound

open NSFormalization.Paper1.PeriodicPicardBilinear
open scoped BigOperators

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

theorem norm_convolutionCoeff_le
    (f g : FiniteFourier) (n : PeriodicFrequency) :
    ‖convolutionCoeff f g n‖ ≤
      Finset.sum (f.support.filter (fun k => g (n - k) ≠ 0)) (fun k => ‖f k‖ * ‖g (n - k)‖) := by
  classical
  unfold convolutionCoeff
  calc
    ‖Finset.sum (f.support.filter (fun k => g (n - k) ≠ 0)) (fun k => f k * g (n - k))‖ ≤
        Finset.sum (f.support.filter (fun k => g (n - k) ≠ 0)) (fun k => ‖f k * g (n - k)‖) :=
      norm_sum_le _ _
    _ = Finset.sum (f.support.filter (fun k => g (n - k) ≠ 0)) (fun k => ‖f k‖ * ‖g (n - k)‖) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]

end NSFormalization.Paper1.PeriodicFinitePicardCoeffBound
