import NSFormalization.Section3.T22.CutoffMultiplier

noncomputable section

namespace NSFormalization.Section3.T22

open MeasureTheory NavierStokes.ProblemStatement
open NavierStokes.R3ConvolutionYoung (scalarConvolution)

-- Negative mutation: replace the main theorem's positive kernel-mass constant by zero.
example (s : ℝ) (K g : Space → ℂ)
    (hK : Integrable (fun ζ : Space ↦ besselW |s| ζ * ‖K ζ‖))
    (hg : MemLp (fun η : Space ↦ (besselW s η : ℝ) • g η) 2 volume) :
    eLpNorm (fun ξ : Space ↦
      (besselW s ξ : ℝ) • scalarConvolution K g ξ) 2 volume ≤
        0 * eLpNorm (fun η : Space ↦ (besselW s η : ℝ) • g η) 2 volume := by
  exact eLpNorm_besselWeight_scalarConvolution_le s K g hK hg

end NSFormalization.Section3.T22
