import NSFormalization.Section4.R43.CriticalDatumPath

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField ClassicalSolutionR MemForceR)

noncomputable section
namespace NSFormalization.Section4.R43

/- Deliberate negative mutation: eq:Rcritical1 requires `ν - C₀ y`, not
`ν + C₀ y`.  Applying the lane's corollary must therefore fail. -/
example
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T)
    (hf : MemForceR f)
    (hinputs : CriticalDatumInputs w hf) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative (criticalDatumPath w hf hinputs) t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative (criticalDatumPath w hf hinputs) t / 2 +
            (ν + trilinearConst * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t :=
  rcritical1_of_classical w hf hinputs

end NSFormalization.Section4.R43
