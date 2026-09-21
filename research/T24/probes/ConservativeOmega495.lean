import NSFormalization.Section3.T24.ConservativeOmega

noncomputable section
open Set NavierStokes.ProblemStatement
open NSFormalization.Section3.T23 NSFormalization.Section3.T24
open NSFormalization.Section4.A02 (SpaceTimeScalar)
open scoped ContDiff

/-- Independent uniqueness route; the canonical proof instead uses energy. -/
theorem zero_from_restOmega_uniqueness_probe
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (Ω : Set Space)
    (hΩ : IsBoundedBoxOrSmoothDomain Ω) (φ : SpaceTimeScalar)
    (hφ : ContDiff ℝ ∞ φ)
    (u : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T)
    (t : ℝ) (ht : t ∈ Ico 0 T) (x : Space) (hx : x ∈ Ω) :
    u.velocity (t, x) = 0 := by
  exact velocity_eq_of_ibp hν (ibp_boundedDomain hΩ) hΩ.1 hΩ.2.1 u
    (restSolutionOmega ν Ω hΩ φ hφ T hT) (by simpa using ht) hx

#print axioms zero_from_restOmega_uniqueness_probe
