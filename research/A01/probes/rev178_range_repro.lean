import NSFormalization.Section4.A01.DatumPathSmooth

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerMeanOrdinaryLift EulerCylinderSobolevSpace
open EulerVolterraConvolution EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A01
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Regression probe for the old range defect: R2's minimal q = 6 case has
-- m + 2 ≤ q + 1, while the former max 6 m + 2 ≤ q + 1 premise was false.
-- This file intentionally must compile after datumPath_contDiffOn_one is sharpened.
example {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 7)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 6))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 7 (0, θ) (u t) = u t)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 (by norm_num : 6 ≤ 6) f) u₀ u t) :
    ∃ G : ℝ → RealVectorSobolev ((0 : ℕ) : ℝ),
      ContDiffOn ℝ 1 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum ((0 : ℕ) : ℝ) (⇑(U t)) (G t.1) := by
  exact datumPath_contDiffOn_one (q := 6) (m := 0)
    (by norm_num) (by norm_num) hν hS u₀ f u U hU hu hduh

end
