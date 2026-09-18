import Contracts.V1.AffineVariation
import Bindings.AffineVariation
import TestSupport.Axioms

/-!
# Tests for `T04.affine_variation`

The checked records are the thirteen-field API at the packet the `I01.packet`
binding selects and the existence form quantified over every viscosity, packet
and admissible cylinder.  The examples below repeat three field shapes of
`research/T24/Spec.lean` and then instantiate the API on the concrete cylinder
`ball 0 1 × (1/4,3/4)` at two concrete perturbations: the zero variation, which
shows the admissible class is inhabited, and lane 417's curl bump
`∇ × (θ(t) φ(x) e₁)`, which is certified **nonzero**, so the five correction
terms of `affineForce` are actually present.
-/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal Topology

/-- The implementation supplies all thirteen fields of the affine-variation
contract at the registered packet. -/
theorem checkedAffineVariation (ν : ℝ) (hν : 0 < ν) (c : Space) {r τ₀ τ₁ : ℝ}
    (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    AffineVariationAPI (Bindings.packet ν hν) c r τ₀ τ₁ :=
  Bindings.affineVariationPacket ν hν c hr hτ₀ hτ₀τ₁ hτ₁

run_cmd TestSupport.checkAxioms ``checkedAffineVariation

/-- The existence form of `prop:affine`, for every viscosity, every packet and
every admissible cylinder. -/
theorem checkedAffineVariationStatement : affineVariationStatement :=
  Bindings.affineVariationStatement_holds

run_cmd TestSupport.checkAxioms ``checkedAffineVariationStatement

/-! ## Independent conformance with `research/T24/Spec.lean` -/

/-- `Spec.lean:1047` `momentum`. -/
example (ν : ℝ) (hν : 0 < ν) (c : Space) {r τ₀ τ₁ : ℝ}
    (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        navierStokesResidual ν
            (affineVelocity (Bindings.packet ν hν).velocity b)
            (affinePressure (Bindings.packet ν hν).pressure) t x =
          affineForce ν (Bindings.packet ν hν).velocity
            (Bindings.packet ν hν).force b (t, x) :=
  (checkedAffineVariation ν hν c hr hτ₀ hτ₀τ₁ hτ₁).momentum

/-- `Spec.lean:1076` `energy_finite`. -/
example (ν : ℝ) (hν : 0 < ν) (c : Space) {r τ₀ τ₁ : ℝ}
    (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
      energyENorm 1 (affineVelocity (Bindings.packet ν hν).velocity b) < ⊤ :=
  (checkedAffineVariation ν hν c hr hτ₀ hτ₀τ₁ hτ₁).energy_finite

/-- `Spec.lean:1085` `infinite_dimensional`. -/
example (ν : ℝ) (hν : 0 < ν) (c : Space) {r τ₀ τ₁ : ℝ}
    (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    ∃ b : ℕ → SpaceTimeField,
      (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b :=
  (checkedAffineVariation ν hν c hr hτ₀ hτ₀τ₁ hτ₁).infinite_dimensional

/-! ## Non-vacuity on the concrete cylinder `ball 0 1 × (1/4,3/4)` -/

/-- Time bump: plateau radius `1/16`, support radius `1/8`, centred at `1/2`. -/
def affineTestTimeBump : ContDiffBump ((1 : ℝ) / 2) :=
  ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

/-- Spatial bump: plateau radius `1/2`, support radius `3/4`, centred at `0`. -/
def affineTestSpaceBump : ContDiffBump (0 : Space) :=
  ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

/-- The nonzero admissible variation `b = ∇ × (θ(t) φ(x) e₁)` of lane 417. -/
def affineTestWitness : SpaceTimeField :=
  NSFormalization.Section3.T24.AffineWitness.curlBump
    affineTestTimeBump affineTestSpaceBump

theorem affineTestWitness_admissible :
    AffineAdmissible (0 : Space) 1 (1 / 4) (3 / 4) affineTestWitness := by
  refine NSFormalization.Section3.T24.AffineWitness.curlBump_admissible
    affineTestTimeBump affineTestSpaceBump ?_ ?_
  · show Metric.closedBall ((1 : ℝ) / 2) (1 / 8) ⊆ Ioo (1 / 4 : ℝ) (3 / 4)
    rw [Real.closedBall_eq_Icc]
    exact Icc_subset_Ioo (by norm_num) (by norm_num)
  · show Metric.closedBall (0 : Space) (3 / 4) ⊆ Metric.ball (0 : Space) 1
    exact Metric.closedBall_subset_ball (by norm_num)

theorem affineTestWitness_ne_zero : affineTestWitness ≠ 0 :=
  NSFormalization.Section3.T24.AffineWitness.curlBump_ne_zero
    affineTestTimeBump affineTestSpaceBump

/-- The zero variation is admissible, so the `∀ b` of every field is not empty,
and at it the affine velocity is the packet velocity itself. -/
theorem affineTestZero_admissible :
    AffineAdmissible (0 : Space) 1 (1 / 4) (3 / 4) (0 : SpaceTimeField) := by
  refine ⟨contDiff_zero_fun, HasCompactSupport.zero, ?_, ?_⟩
  · simp
  · intro t x
    simp [spatialDivergence, spatialDerivative]

/-- At the **nonzero** curl-bump variation the registered record delivers the
momentum equation, the smooth compactly supported corrected force, the finite
energy and the two non-isolation limits. -/
example (ν : ℝ) (hν : 0 < ν) :
    ContDiff ℝ ∞ (affineForce ν (Bindings.packet ν hν).velocity
        (Bindings.packet ν hν).force affineTestWitness) ∧
      CompactPositiveTimeSupport (affineForce ν (Bindings.packet ν hν).velocity
        (Bindings.packet ν hν).force affineTestWitness) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        navierStokesResidual ν
            (affineVelocity (Bindings.packet ν hν).velocity affineTestWitness)
            (affinePressure (Bindings.packet ν hν).pressure) t x =
          affineForce ν (Bindings.packet ν hν).velocity
            (Bindings.packet ν hν).force affineTestWitness (t, x)) ∧
      energyENorm 1 (affineVelocity (Bindings.packet ν hν).velocity
        affineTestWitness) < ⊤ ∧
      (∀ m : ℕ,
        Filter.Tendsto (fun lam : ℝ => ckSeminormE (tsupport affineTestWitness) m
            (fun z => affineVelocity (Bindings.packet ν hν).velocity
              (lam • affineTestWitness) z - (Bindings.packet ν hν).velocity z))
          (𝓝 0) (𝓝 0) ∧
        Filter.Tendsto (fun lam : ℝ => ckSeminormE (tsupport affineTestWitness) m
            (fun z => affineForce ν (Bindings.packet ν hν).velocity
              (Bindings.packet ν hν).force (lam • affineTestWitness) z -
                (Bindings.packet ν hν).force z))
          (𝓝 0) (𝓝 0)) ∧
      affineTestWitness ≠ 0 := by
  have hapi := checkedAffineVariation ν hν (0 : Space) (r := 1) (τ₀ := 1 / 4)
    (τ₁ := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hapi.force_smooth _ affineTestWitness_admissible,
    hapi.force_support _ affineTestWitness_admissible,
    hapi.momentum _ affineTestWitness_admissible,
    hapi.energy_finite _ affineTestWitness_admissible,
    hapi.nonisolated _ affineTestWitness_admissible affineTestWitness_ne_zero,
    affineTestWitness_ne_zero⟩

/-- At the zero variation the energy clause is the packet's own `‖U‖_{E_1} < ∞`,
which `Contracts.V1.PacketAPI` does not carry as a field: the binding assembles
it from `square_integrable`, `energy_isLUB`, `velocity_support` and
`dissipation_integrable`. -/
example (ν : ℝ) (hν : 0 < ν) :
    energyENorm 1 (Bindings.packet ν hν).velocity < ⊤ := by
  have hapi := checkedAffineVariation ν hν (0 : Space) (r := 1) (τ₀ := 1 / 4)
    (τ₁ := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := hapi.energy_finite _ affineTestZero_admissible
  have hzero : affineVelocity (Bindings.packet ν hν).velocity (0 : SpaceTimeField) =
      (Bindings.packet ν hν).velocity := by
    funext z
    simp [affineVelocity]
  rwa [hzero] at h

end BlowupDensity.Tests
