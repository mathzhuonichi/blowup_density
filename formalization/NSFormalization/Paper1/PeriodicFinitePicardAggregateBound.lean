import NSFormalization.Paper1.PeriodicFiniteVectorBound

noncomputable section
namespace NSFormalization.Paper1.PeriodicFinitePicardAggregateBound

open NSFormalization.Paper1.PeriodicFiniteVectorBound
open NSFormalization.Paper1.PeriodicPicardBilinear
open scoped BigOperators

abbrev FiniteVector := PeriodicFiniteVectorBound.FiniteVector

/-!
This file records a pointwise bound for the componentwise finite Fourier
carrier used by the Picard bookkeeping layer.  The operation is deliberately
componentwise; it is not the Navier--Stokes cross-component bilinear term.
-/

def componentwiseConvolutionBound (v w : FiniteVector)
    (n : PeriodicFrequency) : ℝ :=
  ∑ i : Fin 3,
    (∑ k ∈ (v i).support.filter (fun k => (w i) (n - k) ≠ 0),
      ‖(v i) k‖ * ‖(w i) (n - k)‖)

theorem vectorConvolutionL1_le_componentwiseConvolutionBound
    (v w : FiniteVector) (n : PeriodicFrequency) :
    vectorConvolutionL1 v w n ≤ componentwiseConvolutionBound v w n := by
  unfold componentwiseConvolutionBound
  exact vectorConvolutionL1_le v w n

theorem componentwiseConvolutionBound_nonneg
    (v w : FiniteVector) (n : PeriodicFrequency) :
    0 ≤ componentwiseConvolutionBound v w n := by
  unfold componentwiseConvolutionBound
  exact Finset.sum_nonneg (fun i hi =>
    Finset.sum_nonneg (fun k hk =>
      mul_nonneg (norm_nonneg ((v i) k)) (norm_nonneg ((w i) (n - k)))))

end NSFormalization.Paper1.PeriodicFinitePicardAggregateBound
