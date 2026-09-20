import NSFormalization.Section3.T23.Differences

noncomputable section
set_option autoImplicit false

namespace NSFormalization.Section3.T23.DifferencesCloses

open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T22 (zeroExtension)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

variable {ν : ℝ} {u : VelocityField} {p : PressureField}
variable {f : VelocityField} {K Ω : Set Space}
variable (place : DomainPlacementData u p f K)
variable {a : SpatialField} {g : SpaceTimeField}
variable {r δ base packetRadius : ℝ} {D : CutoffData}
variable (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
variable {velocity : ℝ → VelocityField} {force : ℝ → VelocityField}

variable (core : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
variable (hK : IsCompact K)
variable (hu : ∀ s ∈ Ico (0 : ℝ) 1,
  tsupport (fun x : Space => u (s, x)) ⊆ K)
variable (hcarrier : K ⊆ ball (0 : Space) packetRadius)
variable (hpacketForce : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
variable (hbaseD : base ≤ D.ε₀) (hbasePlace : base ≤ place.ε₀)
variable (hΩ : IsOpen Ω) (hδ : 0 < δ)
variable (hball : closure (ball place.chartCenter place.chartRadius) ⊆ Ω)
variable (hvelocity : ∀ ε : ℝ, ∀ z : SpaceTime,
  velocity ε z = reference.velocity z + D.correction ε z +
    scaledVelocity u place.x₀ place.T ε z)
variable (hforce : ∀ ε : ℝ, ∀ z : SpaceTime,
  force ε z = g z + correctionForce ν reference.velocity D ε z +
    scaledForce f place.x₀ place.T ε z)

local notation "εstar" =>
  differenceThreshold place base D.θRadius packetRadius
local notation "ρ" => diffSupportRadius D.θRadius packetRadius

/- `BoundaryInsertionAPI.collar_agreement`. -/
example : ∀ ε ∈ Ioc (0 : ℝ) εstar,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      x ∉ ball place.chartCenter place.chartRadius →
        velocity ε (t, x) = reference.velocity (t, x) := by
  exact collar_agreement place core hK hu hcarrier hbaseD hvelocity

/- `BoundaryInsertionAPI.noSlip_preserved`. -/
example : ∀ ε ∈ Ioc (0 : ℝ) εstar,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ frontier Ω,
      velocity ε (t, x) = 0 := by
  exact noSlip_preserved place reference core hΩ hδ hball hK hu hcarrier
    hbaseD hvelocity

/- `BoundaryInsertionAPI.velocityDifference_divFree`. -/
example
    (hvs : ∀ ε ∈ Ioc (0 : ℝ) εstar,
      SmoothOnClosedSlab (Ico (0 : ℝ) place.T) Ω (velocity ε))
    (hinc : ∀ ε ∈ Ioc (0 : ℝ) εstar,
      ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ Ω,
        spatialDivergence (velocity ε) t x = 0) :
    ∀ ε ∈ Ioc (0 : ℝ) εstar,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ Ω,
      spatialDivergence
        (fun z => velocity ε z - reference.velocity z) t x = 0 := by
  exact velocityDifference_divFree (δ := δ) (ε₀ := εstar)
    (velocity := velocity) place reference hδ hvs hinc

/- `BoundaryInsertionAPI.diffSupportRadius`. -/
example : ℝ := by
  exact ρ

/- `BoundaryInsertionAPI.diffSupportRadius_pos`. -/
example : 0 < ρ := by
  exact diffSupportRadius_pos core.theta_radius_pos

/- `BoundaryInsertionAPI.velocityDifference_support`. -/
example : ∀ ε ∈ Ioc (0 : ℝ) εstar,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      tsupport (fun x : Space => velocity ε (t, x) - reference.velocity (t, x)) ⊆
        ball place.x₀ (ε * ρ) := by
  exact velocityDifference_support core hK hu hcarrier
    ((differenceThreshold_le_base place base D.θRadius packetRadius).trans hbaseD)
    hvelocity

/- `BoundaryInsertionAPI.diffSupport_in_chart`. -/
example : ∀ ε ∈ Ioc (0 : ℝ) εstar,
    ball place.x₀ (ε * ρ) ⊆
      ball place.chartCenter place.chartRadius := by
  exact diffSupport_in_chart place base D.θRadius packetRadius core.theta_radius_pos

/- `BoundaryInsertionAPI.forceDifference_spatialSupport`. -/
example : ∀ ε ∈ Ioc (0 : ℝ) εstar,
    ∀ t : ℝ, ∀ x : Space, force ε (t, x) - g (t, x) ≠ 0 →
      x ∈ closure (ball place.chartCenter place.chartRadius) := by
  exact forceDifference_spatialSupport place core hpacketForce hbaseD hbasePlace hforce

/- The closed support required by the downstream T22 comparison. -/
example : ∀ ε ∈ Ioc (0 : ℝ) εstar, ∀ t : ℝ,
    tsupport (zeroExtension Ω
      (fun x : Space => force ε (t, x) - g (t, x))) ⊆
        closure (ball place.chartCenter place.chartRadius) := by
  exact forceDifference_zeroExtension_support place core hpacketForce hbaseD
    hbasePlace hforce

end NSFormalization.Section3.T23.DifferencesCloses
