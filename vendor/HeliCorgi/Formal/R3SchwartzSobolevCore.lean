import Formal.R3SchwartzConvection
import Formal.R3SobolevCarrier

namespace MNS2

open MeasureTheory
open scoped SchwartzMap LineDeriv

noncomputable section

/-- The complex Bessel weight used to place a Schwartz field in the `H^s` coordinate carrier. -/
def r3SobolevWeightComplex (s : ℝ) (ξ : R3) : ℂ :=
  Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2))

/-- The Bessel weight has temperate growth for every real Sobolev order. -/
theorem r3SobolevWeightComplex_hasTemperateGrowth (s : ℝ) :
    (r3SobolevWeightComplex s).HasTemperateGrowth := by
  unfold r3SobolevWeightComplex
  fun_prop

/--
Canonical continuous embedding of the Schwartz core into the repository's `H^s` Bessel-coordinate
carrier.  The stored coordinate is exactly `J^s f` in `L²`.
-/
def r3SchwartzToHsCLM (s : ℝ) :
    R3SchwartzVelocity →L[ℂ] R3HsVelocity s :=
  (SchwartzMap.toLpCLM ℂ R3C 2 (volume : Measure R3)).comp
    (SchwartzMap.fourierMultiplierCLM R3C
      (fun ξ : R3 => Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2))))

@[simp]
theorem r3SchwartzToHsCLM_apply (s : ℝ) (f : R3SchwartzVelocity) :
    r3SchwartzToHsCLM s f =
      (SchwartzMap.fourierMultiplierCLM R3C
        (fun ξ : R3 => Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2))) f).toLp 2 := by
  rfl

/--
Applying the Bessel potential `J^s` to a Schwartz field gives exactly the tempered distribution
represented by its stored `H^s` coordinate.
-/
theorem besselPotential_schwartz_eq_r3SchwartzToHs_coordinate
    (s : ℝ) (f : R3SchwartzVelocity) :
    TemperedDistribution.besselPotential R3 R3C s (f : 𝓢'(R3, R3C)) =
      r3L2ToTemperedCLM (r3SchwartzToHsCLM s f) := by
  have h :=
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
      (F := R3C)
      (g := fun ξ : R3 => Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2)))
      (by fun_prop) f
  simpa [r3L2ToTemperedCLM, r3SchwartzToHsCLM,
    TemperedDistribution.besselPotential] using h

/-- Decoding the canonical `H^s` coordinate recovers the original Schwartz field exactly in `𝓢'`. -/
theorem r3HsToTempered_r3SchwartzToHsCLM
    (s : ℝ) (f : R3SchwartzVelocity) :
    r3HsToTemperedCLM s (r3SchwartzToHsCLM s f) = (f : 𝓢'(R3, R3C)) := by
  rw [r3HsToTemperedCLM_apply]
  rw [← besselPotential_schwartz_eq_r3SchwartzToHs_coordinate s f]
  rw [TemperedDistribution.besselPotential_besselPotential_apply]
  simp

/-- The concrete coordinate derivative agrees with the distributional directional derivative. -/
theorem r3SchwartzCoordinateDerivative_toTempered
    (i : Fin 3) (v : R3SchwartzVelocity) :
    ((r3SchwartzCoordinateDerivative i v : R3SchwartzVelocity) : 𝓢'(R3, R3C)) =
      ∂_{r3CoordinateDirection i} (v : 𝓢'(R3, R3C)) := by
  symm
  simpa [r3SchwartzCoordinateDerivative] using
    (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
      (μ := (volume : Measure R3)) v (r3CoordinateDirection i))

/-- One coordinate derivative loses exactly one Sobolev order at the distributional interface. -/
theorem r3SchwartzCoordinateDerivative_memSobolev_of_memSobolev
    (s : ℝ) (i : Fin 3) (v : R3SchwartzVelocity)
    (hv : TemperedDistribution.MemSobolev s 2 (v : 𝓢'(R3, R3C))) :
    TemperedDistribution.MemSobolev (s - 1) 2
      ((r3SchwartzCoordinateDerivative i v : R3SchwartzVelocity) : 𝓢'(R3, R3C)) := by
  rw [r3SchwartzCoordinateDerivative_toTempered]
  exact hv.lineDerivOp

/-- The literal Schwartz convection output belongs to every Sobolev order. -/
theorem r3SchwartzConvection_memSobolev
    (s : ℝ) (u v : R3SchwartzVelocity) :
    TemperedDistribution.MemSobolev s 2
      (r3SchwartzConvection u v : 𝓢'(R3, R3C)) := by
  exact SchwartzMap.memSobolev (r3SchwartzConvection u v)

/--
The exact analytic estimate still needed to extend physical convection from the Schwartz core to the
strong Sobolev carrier.  For integer `m ≥ 3`, proving this proposition is the genuine
`H^m × H^m → H^(m-1)` product-estimate gate; this definition does not assume or prove it.
-/
def R3SchwartzConvectionSobolevEstimate (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : R3SchwartzVelocity,
    ‖r3SchwartzToHsCLM ((m : ℝ) - 1) (r3SchwartzConvection u v)‖ ≤
      C * ‖r3SchwartzToHsCLM (m : ℝ) u‖ * ‖r3SchwartzToHsCLM (m : ℝ) v‖

end

end MNS2
