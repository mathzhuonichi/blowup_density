import Euler.MeanPacketForcingAlgebra
import Euler.MeanPacketProvider
import Euler.LpSmoothCoefficientContinuity

/-! Actual multiplication closure for admissible mean forcing. -/

noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketProfileRecursion
  EulerLpSmoothCoefficientProduct

variable {D : Data} {raw : VectorField}

/-- Multiplying the raw field by a genuinely bounded smooth coefficient path
preserves all actual L² spatial jets and their time continuity. -/
def multiply (G : Forcing D raw) (A : SmoothCoefficientPath (Icc (0 : ℝ) D.T) (Space →L[ℝ] Space)) :
    Forcing D (fun z => A.field (D.clamp z.1) z.2.1 (raw z)) :=
  ofSlices (fun r => product A (D.clamp r) (G.slices r))
    (fun n => by
      simpa only [Data.clamp_coe] using continuous_product_jet A
        (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous n)
    (fun t x θ => by rw [G.raw_eq t x θ]; rfl)

end EulerMeanPacketProvider.Forcing
