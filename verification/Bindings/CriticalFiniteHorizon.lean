import Contracts.V1.CriticalFiniteHorizon
import Bindings.MaximalPartial
import NSFormalization.Section4.R44.Prop44

/-!
# Binding for Proposition 4.4

The implementation supplies the exact nine-field finite-horizon API with
`c = R44.theta / 20`, `C = 3`, and its named `R44.radius`.  Force vocabulary is
definitionally the registered `Contracts.V1.Data` vocabulary.  Lifespan and
breakdown-set conclusions use the established A02/Data solution-structure
bridge because their two `ClassicalSolutionR` structures are not definitionally
equal.
-/

noncomputable section

namespace BlowupDensity.Bindings

open BlowupDensity.Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal

section Correspondence

variable (s : ℝ) (f : SpaceTimeField)

/-- The contract's force class is the A02-local restatement consumed by R44. -/
theorem criticalFiniteHorizon_memForceR_eq :
    MemForceR f = A02.MemForceR f := rfl

/-- The contract's inhomogeneous `L²` force norm is R44's implementation norm. -/
theorem criticalFiniteHorizon_forceSobolevENormL2_eq :
    forceSobolevENormL2 s f = R44.forceSobolevENormL2 s f := rfl

end Correspondence

/-- The implementation's coefficient is the advertised `theta / 20`. -/
theorem criticalFiniteHorizon_radiusCoefficient_eq :
    R44.radiusCoefficient = R44.theta / 20 := by
  norm_num [R44.radiusCoefficient, R44.C₃]

/-- The implementation's exponential rate is the advertised constant `3`. -/
theorem criticalFiniteHorizon_radiusRate_eq : R44.radiusRate = 3 := by
  norm_num [R44.radiusRate, R44.C₂]

/-- Breakdown-set membership transports through the same maximal-lifespan
bridge as the theorem conclusion. -/
theorem criticalFiniteHorizon_breakdownSetRZero_iff (ν T : ℝ) (f : SpaceTimeField) :
    f ∈ breakdownSetRZero ν T ↔ f ∈ R41.breakdownSetRZero ν T := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    rw [maximalPartial_maximalLifespanR_eq]
    exact hf.2
  · intro hf
    refine ⟨hf.1, ?_⟩
    rw [← maximalPartial_maximalLifespanR_eq]
    exact hf.2

/-- Proposition 4.4 in the registered vocabulary, with its explicit universal
constants and named finite-horizon radius. -/
def criticalFiniteHorizon :
    Contracts.V1.CriticalFiniteHorizon.CriticalFiniteHorizonAPI :=
  { c := R44.theta / 20
    C := 3
    hc := div_pos R44.theta_pos (by norm_num)
    hC := by norm_num
    radius := R44.radius
    radiusFormula := fun ν S => by
      unfold R44.radius
      rw [criticalFiniteHorizon_radiusCoefficient_eq,
        criticalFiniteHorizon_radiusRate_eq]
    radiusPos := fun _ _ hν _ => R44.radius_pos hν
    main := fun ν S hν hS f hf hsmall => by
      rw [← maximalPartial_maximalLifespanR_eq]
      exact R44.main ν S hν hS f hf hsmall
    nonDensityBallZero := fun ν T hν hT f hf hsmall hb =>
      R44.nonDensityBallZero ν T hν hT f hf hsmall
        ((criticalFiniteHorizon_breakdownSetRZero_iff ν T f).mp hb) }

end BlowupDensity.Bindings
