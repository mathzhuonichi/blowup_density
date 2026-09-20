import NSFormalization.Section3.T23.Lifespan

/-! Exact U8 field targets from Boundary.lean (the canonical adapter of
Spec.lean:847,857,863,868). No BoundaryInsertionAPI witness is assumed.
All four conclusions are synthesized from U3/U4 family facts and packet speed.
The box examples discharge IBP; the general examples expose it explicitly. -/
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
open NSFormalization.Source.PacketScaling (SpeedUnboundedAt)
namespace U8FieldProbe

variable {U f : VelocityField} {p : PressureField} {K Ω : Set Space}
  (place : DomainPlacementData U p f K) (D : CutoffData)
  {ν δ : ℝ} {a : NSFormalization.Section4.A02.SpatialField} {g : VelocityField}
  (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
  {ε₀ : ℝ} {velocity force : ℝ → VelocityField} {pressure : ℝ → PressureField}
  (hspeed : SpeedUnboundedAtOne U) (hscale : ε₀ ≤ place.ε₀)
  (hball : closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω)
  (hformula : ∀ ε z, velocity ε z = reference.velocity z + D.correction ε z +
    NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε z)
  (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) place.T,
    tsupport (fun x => NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε (t, x)) ⊆
      Metric.ball place.chartCenter place.chartRadius)
  (hcancel : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (place.T - ε ^ 2) place.T,
    ∀ x ∈ tsupport (fun y => NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε (t, y)),
      reference.velocity (t, x) + D.correction ε (t, x) = 0)
  (hsolution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ w : ClassicalSolutionOmega ν Ω a (force ε) place.T,
      w.velocity = velocity ε ∧ w.pressure = pressure ε)

include hspeed hscale hball hformula hsupport hcancel

-- BoundaryInsertionAPI.blowup / Spec:863.
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀, SpeedUnboundedAt place.T (velocity ε) := by
  exact U8.blowup place D reference hspeed hscale hball hformula hsupport hcancel

include hsolution
-- BoundaryInsertionAPI.blowup_limsup / Spec:868.
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    NSFormalization.Section4.A02.limsupLeft place.T
      (fun t => NSFormalization.Section4.A02.speedENorm (fun x : Space => velocity ε (t, x))) = ⊤ := by
  exact U8.blowup_limsup place D reference hspeed hscale hball hformula hsupport hcancel hsolution

variable (hν : 0 < ν) (hΩ : IsBoundedBoxOrSmoothDomain Ω) (hI : IBP Ω)
include hν hΩ hI

-- BoundaryInsertionAPI.lifespan / Spec:847; smooth G1 is explicit.
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T := by
  exact U8.lifespan place D reference hspeed hscale hball hformula hsupport hcancel hsolution hν hΩ.1 hΩ.2.1 hI

-- BoundaryInsertionAPI.maximal / Spec:857; actual total fields are retained.
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalDomainSolution ν Ω a (force ε) (velocity ε) (pressure ε) := by
  exact U8.maximal place D reference hspeed hscale hball hformula hsupport hcancel hsolution hν hΩ.1 hΩ.2.1 hI

omit hΩ hI in
example (hbox : IsBoxDomain Ω) : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T := by
  exact U8.lifespan_box place D reference hspeed hscale hball hformula hsupport hcancel hsolution hν hbox

omit hΩ hI in
example (hbox : IsBoxDomain Ω) : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalDomainSolution ν Ω a (force ε) (velocity ε) (pressure ε) := by
  exact U8.maximal_box place D reference hspeed hscale hball hformula hsupport hcancel hsolution hν hbox

end U8FieldProbe
