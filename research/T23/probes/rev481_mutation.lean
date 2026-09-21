import NSFormalization.Section3.T23.MatchingSupplier

noncomputable section
namespace Rev481

open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
open scoped ContDiff

/-- Deliberately false mutation: widen the scale interval from `(0,e]` to
`(-1,e]`. Reusing the production proof must fail because positivity of `ε` is
load-bearing in the cutoff and rescaling argument. -/
example {ν : ℝ} {u v : VelocityField} {K : Set Space}
    (C : WholeSpaceCorrectionAPI ν u K) (hK : IsCompact K)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ ball C.x₀ C.r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (C.T + C.δ), ∀ x ∈ ball C.x₀ C.r,
      spatialDivergence v t x = 0)
    (hu : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    {e : ℝ} (he : e ≤ C.ε₀) :
    let D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius e
    ∀ ε ∈ Ioc (-1 : ℝ) e, ∀ t ∈ Ico (0 : ℝ) C.T, ∀ x : Space,
      spatialDerivative (NSFormalization.Section3.T15.scaledVelocity u C.x₀ C.T ε) t x
        (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) = 0 := by
  intro D ε hε t ht x
  exact (C.local_crossTransport hK hv hdiv hu he ε hε t ht x).1

end Rev481
