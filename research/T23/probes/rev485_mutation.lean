import NSFormalization.Section3.T23.Rates

noncomputable section
namespace Rev485Mutation

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
open scoped ENNReal Topology

variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K Ω : Set Space} {a : Space → Space} {g : VelocityField}
    (place : DomainPlacementData u p f K) {δ : ℝ} (D : CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (force : ℝ → VelocityField) (ε₀ : ℝ) (A B : ℝ → ℝ)
    (he1 : ε₀ ≤ 1)
    (hformula : ∀ ε z, force ε z = g z + correctionForce ν reference.velocity D ε z +
      NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε z)
    (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t,
      Function.support (fun x => force ε (t, x) - g (t, x)) ⊆ Ω)
    (hleft : ∀ s, ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
        zeroExtForceSobolevENorm Ω s (fun z => force ε z - g z))
    (hF : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, 0 ≤ t → Continuous
      (fun x => NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε (t, x)))
    (hH : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, 0 ≤ t → Continuous
      (fun x => correctionForce ν reference.velocity D ε (t, x)))
    (hpacket : ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section4.D01.forceSobolevENorm 1 s
        (NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε) ≤
      ENNReal.ofReal (A s * (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))))
    (hcorr : ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section4.D01.forceSobolevENorm 1 s
        (correctionForce ν reference.velocity D ε) ≤
      ENNReal.ofReal (B s * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))))

/-- Negative mutation: flip the sign of the proved positive main constant. -/
example :
    ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
        ENNReal.ofReal (-forceDiffSobolevConst A B s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) := by
  exact forceDifference_sobolev_bound place D reference force ε₀ A B he1
    hformula hsupport hleft hF hH hpacket hcorr

end Rev485Mutation
