import Contracts.V2.EnergyHighPartial
import Bindings.EnergyHighPartialV2
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one test `Tests.EnergyHighPartial` is untouched and keeps running against
`Bindings.energyHighPartial`; this is the second, stronger acceptance test, not a
replacement.  `Bindings.energyHighPartial_of_v2` is the checked link between the two:
it records that the version-two witness projects, by `rfl`, onto the frozen version-one
witness, so nothing that version one guarantees is lost by version two. -/

noncomputable section
namespace BlowupDensity.Tests

open Set MeasureTheory
open Contracts.V1.Data
open Contracts.V1.EnergyHighPartial (sobolevNormAt HasSmoothSobolevPath)
open Contracts.V2.EnergyHighPartial (MemL1Hm)

/-- An implementation must supply every field of the unchanged version-one
specification **and** the continuation constant `Cgron`/`Cgron_pos` and the two
`ζ`-continuation fields of lanes 135 and 138 (`regularizedNormDerivative`,
`highContinuationIntegral`).  `EnergyHighPartialV2API` carries data fields, so this is
a `def`. -/
def checkedEnergyHighPartialV2 :
    Contracts.V2.EnergyHighPartial.EnergyHighPartialV2API :=
  Bindings.energyHighPartialV2

run_cmd TestSupport.checkAxioms ``checkedEnergyHighPartialV2

/-- `regularizedNormDerivative`, in the manuscript's shape
(`appendix-a-local-theory.tex:139-145`, eq:highcontinuation before the `ζ↓0` limit):
`(d/dt)(‖u‖²_{H^m}+ζ²)^{1/2} ≤ C_{m,ν}‖u‖²_{H²}(‖u‖²_{H^m}+ζ²)^{1/2} + ‖f‖_{H^m}`. -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T, ∀ ζ : ℝ, 0 < ζ →
            ∃ d : ℝ,
              HasDerivAt
                  (fun r : ℝ =>
                    Real.sqrt (sobolevNormAt (m : ℝ) w.velocity r ^ 2 + ζ ^ 2)) d t ∧
                d ≤ checkedEnergyHighPartialV2.Cgron m ν *
                      sobolevNormAt 2 w.velocity t ^ 2 *
                      Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2) +
                    sobolevNormAt (m : ℝ) f t :=
  checkedEnergyHighPartialV2.regularizedNormDerivative

/-- `highContinuationIntegral`, in the manuscript's shape
(`appendix-a-local-theory.tex:141-145`, eq:highcontinuation after `ζ↓0`, integrated on
`[t₀,t] ⊆ [0,T)`): the integrand is interval-integrable and
`‖u(t)‖_{H^m} ≤ ‖u(t₀)‖_{H^m} + ∫_{t₀}^{t}(C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m})`. -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t → t < T →
            IntervalIntegrable
                (fun s : ℝ =>
                  checkedEnergyHighPartialV2.Cgron m ν *
                      sobolevNormAt 2 w.velocity s ^ 2 *
                      sobolevNormAt (m : ℝ) w.velocity s +
                    sobolevNormAt (m : ℝ) f s)
                volume t₀ t ∧
              sobolevNormAt (m : ℝ) w.velocity t ≤
                sobolevNormAt (m : ℝ) w.velocity t₀ +
                  ∫ s in t₀..t,
                    (checkedEnergyHighPartialV2.Cgron m ν *
                        sobolevNormAt 2 w.velocity s ^ 2 *
                        sobolevNormAt (m : ℝ) w.velocity s +
                      sobolevNormAt (m : ℝ) f s) :=
  checkedEnergyHighPartialV2.highContinuationIntegral

/-- The continuation constant is strictly positive at every order and positive
viscosity. -/
example : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < checkedEnergyHighPartialV2.Cgron m ν :=
  checkedEnergyHighPartialV2.Cgron_pos

end BlowupDensity.Tests
