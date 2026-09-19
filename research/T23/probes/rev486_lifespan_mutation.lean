import NSFormalization.Section3.T23.Lifespan

noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
namespace Rev486Mutation

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
  (hν : 0 < ν) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hI : IBP Ω)

include hspeed hscale hball hformula hsupport hcancel hsolution hν ho hb hI

/-! Intentional mutation: widening the exact lifespan from `T` to `T + 1`
must not be accepted by the production theorem. -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal (place.T + 1) := by
  exact U8.lifespan place D reference hspeed hscale hball hformula hsupport hcancel
    hsolution hν ho hb hI

end Rev486Mutation
