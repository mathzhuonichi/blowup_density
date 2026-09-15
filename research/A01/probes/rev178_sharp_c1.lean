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

-- Reviewer range probe: C¹ needs only the two orders consumed by the Laplacian.
-- The order-six algebra floor is unnecessary before the residual is differentiated.
theorem rev178_datumPath_contDiffOn_one_sharp {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t) :
    ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 1 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  let v := restrictPath (by omega : m ≤ q + 1) u
  have hres : ContDiffOn ℝ 0
      (extendPath S hS.le (cylinderResidualPath hq hm ν f u)) (Icc (0 : ℝ) S) :=
    contDiffOn_zero.mpr
      (extendPath_continuous S hS.le (cylinderResidualPath hq hm ν f u)).continuousOn
  have hcv : ContDiffOn ℝ 1 (extendPath S hS.le v) (Icc (0 : ℝ) S) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by rfl]
    apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hS)).mpr
    refine ⟨?_, by simp, ?_⟩
    · intro t ht
      exact (cylinderVelocity_hasDerivWithinAt (k := m) hq hm
        hν hS u₀ f u hduh ⟨t, ht⟩).differentiableWithinAt
    · apply hres.congr
      intro t ht
      have hd := cylinderVelocity_hasDerivWithinAt (k := m) hq hm
        hν hS u₀ f u hduh ⟨t, ht⟩
      have hdval := hd.derivWithin ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht)
      calc
        _ = cylinderResidualPath hq hm ν f u ⟨t, ht⟩ := hdval
        _ = _ := by simp only [extendPath, projIcc_of_mem hS.le ht]
  have hv : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 m (0, θ) (v t) = v t := by
    intro θ t
    change sobolevTranslation 1 m (0, θ)
      (restrictOperator 1 (by omega : m ≤ q + 1) (u t)) =
      restrictOperator 1 (by omega : m ≤ q + 1) (u t)
    rw [← restrictOperator_translation, hu θ t]
  have hVU : ∀ t, ordinaryLift (U t) = value 1 (v t) := by
    intro t
    rw [hU]
    exact (value_restrictOperator 1 (by omega : m ≤ q + 1) (u t)).symm
  exact exists_contDiff_datumPath_of_cylinder hS v U hv hVU hcv

end
