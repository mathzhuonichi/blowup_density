import NSFormalization.Paper1.PeriodicFinitePicardCoeffBound

noncomputable section
namespace NSFormalization.Paper1.PeriodicFiniteVectorBound

open NSFormalization.Paper1.PeriodicPicardBilinear
open scoped BigOperators

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier
abbrev FiniteVector := Fin 3 → FiniteFourier

def vectorCoeffL1 (v : FiniteVector) (n : PeriodicFrequency) : ℝ :=
  ∑ i : Fin 3, ‖v i n‖

theorem vectorCoeffL1_nonneg (v : FiniteVector) (n : PeriodicFrequency) :
    0 ≤ vectorCoeffL1 v n := by
  exact Finset.sum_nonneg (fun i hi => norm_nonneg _)

theorem component_norm_le_vectorCoeffL1 (v : FiniteVector) (n : PeriodicFrequency)
    (i : Fin 3) :
    ‖v i n‖ ≤ vectorCoeffL1 v n := by
  unfold vectorCoeffL1
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => ‖v j n‖) (fun j hj => norm_nonneg _) (Finset.mem_univ i)

end NSFormalization.Paper1.PeriodicFiniteVectorBound

namespace NSFormalization.Paper1.PeriodicFiniteVectorBound
open NSFormalization.Paper1.PeriodicPicardBilinear

/-- Aggregate coefficient bound for componentwise finite convolutions. -/
def vectorConvolutionL1 (v w : FiniteVector) (n : PeriodicFrequency) : ℝ :=
  ∑ i : Fin 3, ‖convolutionCoeff (v i) (w i) n‖

theorem vectorConvolutionL1_le (v w : FiniteVector) (n : PeriodicFrequency) :
    vectorConvolutionL1 v w n ≤
      ∑ i : Fin 3, Finset.sum ((v i).support.filter (fun k => (w i) (n-k) ≠ 0))
        (fun k => ‖(v i) k‖ * ‖(w i) (n-k)‖) := by
  unfold vectorConvolutionL1
  apply Finset.sum_le_sum
  intro i hi
  exact NSFormalization.Paper1.PeriodicFinitePicardCoeffBound.norm_convolutionCoeff_le
    (v i) (w i) n

end NSFormalization.Paper1.PeriodicFiniteVectorBound
