import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A04.ZeroSolution
import Euler.OrdinaryCauchyInterpolation
import Euler.SmoothL2Series

noncomputable section

namespace NSFormalization.Section4.A01.Rev192

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerOrdinarySobolev
open EulerSmoothL2Series
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem canonical_zero_initial (q : ℕ) :
    ordinarySobolev q
      (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
      (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine (ordinarySobolev_norm_le_tensor
      (SmoothL2Field.zeroField : SmoothL2Field Space) q).trans ?_
    simp [tensorNorm, zeroField_jet]
  · exact norm_nonneg _

private theorem canonical_zero_force {S : ℝ} (q : ℕ) :
    sobolevPath
      (C01.forcePath (S := S) A04.memForceR_zero)
      (C01.forcePath_jetLp_continuous (S := S) A04.memForceR_zero) q = 0 := by
  apply ContinuousMap.ext
  intro t
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine (ordinarySobolev_norm_le_tensor
      (C01.forcePath (S := S) A04.memForceR_zero t) q).trans ?_
    have hpath : C01.forcePath (S := S) A04.memForceR_zero t =
        (SmoothL2Field.zeroField : SmoothL2Field Space) := by
      unfold C01.forcePath C01.forceSliceField SmoothL2Field.zeroField
      rfl
    rw [hpath]
    simp [tensorNorm, zeroField_jet]
  · exact norm_nonneg _

/-- Genuine satisfiability: zero datum and zero force satisfy the all-order bound for every
nonnegative radius family, without assuming `hb`. -/
theorem zero_all_order_bound (ν S : ℝ) (hν : 0 < ν)
    (R : ℕ → ℝ) (hR : ∀ q, 0 ≤ R q) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (C01.forcePath (S := S) A04.memForceR_zero)
      (C01.forcePath_jetLp_continuous (S := S) A04.memForceR_zero) (R q) := by
  intro q hq T hT hTS u hu
  have hu0 := canonical_zero_initial (q + 1)
  have hf0 := canonical_zero_force (S := S) q
  rw [hu0, hf0] at hu
  have hz : ∀ t, (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) t =
      quadraticDuhamel 1 ν hν hT hTS
        (coefficients 1 hq 0) 0 0 t := by
    intro t
    simp [quadraticDuhamel, source_eq]
  have huz : u = 0 := by
    rcases hT.eq_or_lt with rfl | hTpos
    · apply ContinuousMap.ext
      intro t
      have ht : t.1 = 0 := le_antisymm t.2.2 t.2.1
      rw [hu t]
      simp [quadraticDuhamel, ht]
    · exact quadratic_mild_unique (q := q) hν hTpos
        (coefficients 1 hq 0) 0 u 0 hu hz
  rw [huz, norm_zero]
  exact hR q

/-- The lane's main theorem therefore has a fully concrete zero-data/zero-force instance. -/
example (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S) (R : ℕ → ℝ)
    (hR : ∀ q, 0 ≤ R q) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ =
        (SmoothL2Field.zeroField : SmoothL2Field Space).toLp := by
  have ha : ∀ x, EulerSmoothLimit.divergence
      (SmoothL2Field.zeroField : SmoothL2Field Space).field x = 0 := by
    intro x
    simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField]
  obtain ⟨U, hU0, _hpairs, _hsob⟩ := cylinderPair_of_bounds
    (f := (0 : SpaceTimeField)) A04.memForceR_zero hν hS
    (SmoothL2Field.zeroField : SmoothL2Field Space) ha R
    (zero_all_order_bound ν S hν R hR)
  exact ⟨U, hU0⟩

end NSFormalization.Section4.A01.Rev192
