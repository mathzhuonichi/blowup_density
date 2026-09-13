import NSFormalization.Paper1.PeriodicLerayArbitraryWeight
import NSFormalization.Paper1.PeriodicCrossComponentTransportBilinear

/-! Leray projection applied to the existing finite Fourier transport output. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicProjectedTransport

open NSFormalization.Paper1.PeriodicCrossComponentTransport
open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open NSFormalization.Paper1.PeriodicLerayLinear
open NSFormalization.Paper1.PeriodicLerayArbitraryWeight
open scoped BigOperators
abbrev FV := NSFormalization.Paper1.PeriodicFiniteVectorBound.FiniteVector

def transportVector (u v : FV) : VectorCoeff :=
  fun k i => transportCoeffConv u v i k

def projectedTransport (u v : FV) : VectorCoeff :=
  lerayLinear (transportVector u v)

@[simp] theorem projectedTransport_apply (u v : FV)
    (i : Fin 3) (k : PeriodicFrequency) :
    projectedTransport u v k i = projectedCoeff (transportVector u v) i k := by
  simp [projectedTransport, lerayLinear_apply]

theorem projectedTransport_divergence_free (u v : FV)
    (k : PeriodicFrequency) : divergenceCoeff (projectedTransport u v) k = 0 := by
  exact divergenceCoeff_lerayLinear (transportVector u v) k

theorem projectedTransport_weighted_energy_le
    (S : Finset PeriodicFrequency) (w : PeriodicFrequency → ℝ)
    (hw : ∀ k, 0 ≤ w k) (u v : FV) :
    (∑ k ∈ S, w k * (∑ i : Fin 3,
      ‖projectedTransport u v k i‖ ^ 2)) ≤
      ∑ k ∈ S, w k * (∑ i : Fin 3,
        ‖transportVector u v k i‖ ^ 2) := by
  simpa only [projectedTransport_apply] using
    (finite_arbitrary_weight_sum_sq_norm_projectedCoeff_le S w hw
      (transportVector u v))

end NSFormalization.Paper1.PeriodicProjectedTransport
