import NavierStokes.R3LocalizedPressure
import NavierStokes.R3SpaceTimeApproximation

/-!
# Passing pressure pairings from Gaussian kernels to the physical pressure

The pressure itself may differ by a function of time. Testing against the
spatial divergence of a compact vector field removes precisely that freedom.
-/

noncomputable section
namespace NavierStokes.R3PressurePairing

open Set Filter MeasureTheory TemperedDistribution
open R3SpaceTime R3SpaceTimePressure R3WeakPressure
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal

def testDivergence (Ψ : Fin 3 → 𝓢(Domain, ℂ)) : 𝓢(Domain, ℂ) :=
  ∑ i, ∂_{spaceDirection i} (Ψ i)

/-- Equality of pressure gradients determines the pressure pairing with a
compact divergence test. -/
theorem divergence_test_eq {Q : 𝓢'(Domain, ℂ)} {p : Domain → ℂ}
    (hp : ContDiff ℝ ∞ p)
    (hQ : ∀ i, Represents (∂_{spaceDirection i} Q) (directional (spaceDirection i) p))
    (Ψ : Fin 3 → 𝓢(Domain, ℂ)) (hc : ∀ i, HasCompactSupport (Ψ i : Domain → ℂ)) :
    Q (testDivergence Ψ) = ∫ z : Domain, testDivergence Ψ z * p z := by
  have he (i : Fin 3) : Q (∂_{spaceDirection i} (Ψ i)) =
      ∫ z : Domain, (∂_{spaceDirection i} (Ψ i)) z * p z := by
    have hh := hQ i (Ψ i) (hc i)
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg] at hh
    rw [integration_by_parts (hp.of_le (by simp)) (Ψ i) (hc i) _] at hh
    exact neg_injective hh
  have hi (i : Fin 3) : Integrable (fun z : Domain => (∂_{spaceDirection i} (Ψ i)) z * p z) :=
    ((∂_{spaceDirection i} (Ψ i)).continuous.mul hp.continuous).integrable_of_hasCompactSupport
      (compact_lineDeriv (Ψ i) (hc i) _).mul_right
  simp only [testDivergence, map_sum, sum_apply, Finset.sum_mul, he]
  exact (integral_finsetSum _ (fun i _ => hi i)).symm

/-- The actual Gaussian stress-pressure pairings converge to the physical
pressure pairing for every compact smooth vector test field. -/
theorem actual_pressure_pairing_tendsto (G : Fin 3 → Fin 3 → Domain → ℂ)
    (hG : ∀ i j, MemLp (G i j) 1) (p : Domain → ℂ) (hp : ContDiff ℝ ∞ p)
    (hP : ∀ i, Represents
      (∂_{spaceDirection i} (stressPressure (fun i j => (hG i j).toLp (G i j))))
      (directional (spaceDirection i) p))
    (Ψ : Fin 3 → 𝓢(Domain, ℂ)) (hc : ∀ i, HasCompactSupport (Ψ i : Domain → ℂ)) :
    Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z : Domain, testDivergence Ψ z * R3SpatialConvolution.regularized n i j (G i j) z)
      atTop (𝓝 (∫ z : Domain, testDivergence Ψ z * p z)) := by
  have hh := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      R3SpaceTimeApproximation.actual_regularized_test_tendsto i j (hG i j) (testDivergence Ψ)))
  have he : (∑ i : Fin 3, ∑ j : Fin 3,
      pressureL1 i j ((hG i j).toLp (G i j)) (testDivergence Ψ)) =
      ∫ z : Domain, testDivergence Ψ z * p z := by
    rw [← divergence_test_eq hp hP Ψ hc]
    simp only [stressPressure, sum_apply]
  simpa only [he] using hh

end NavierStokes.R3PressurePairing
