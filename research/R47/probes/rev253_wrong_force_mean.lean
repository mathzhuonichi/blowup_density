import Bindings.FluxCancellation
noncomputable section
namespace BlowupDensity.Bindings
open Set MeasureTheory
open Contracts.V1 (PacketAPI InsertionFamilyAPI Space)
open Contracts.V1.Data
variable {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)
-- Substantive mutation: replace zero force mean by the nonzero coordinate vector e₀.
theorem rev253_wrong_force_mean {ε t : ℝ}
    (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ico 0 A.T)
    (grid : Grid) (k₀ : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k₀) :
    (∫ x in grid.cell k₀, (A.force ε (t,x) - A.g (t,x))) = NavierStokes.ProblemStatement.coordinateVector 0 :=
  forceDifference_cell_integral_zero A (compactMomentumIntegral A) hε ht grid k₀ hB


end BlowupDensity.Bindings
