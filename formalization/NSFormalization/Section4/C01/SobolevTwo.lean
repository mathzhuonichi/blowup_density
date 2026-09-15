import NSFormalization.Section4.C01.EnstrophyBounds
import NSFormalization.Section4.D01.FiniteOrderNorm

/-! The ordinary L² and Laplacian energies control the genuine order-two
angular Sobolev datum. The proof uses weak derivatives and the quantitative
datum constructor, without a pointwise Fourier transform of a non-L¹ field. -/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NSFormalization.Source.OrdinaryViscousStability
open scoped RealInnerProductSpace ENNReal

namespace NSFormalization.Section4.C01

theorem eLpNorm_toReal_sq_eq_l2Sq (Z : SmoothL2Field Space) :
    (eLpNorm Z.field 2 volume).toReal ^ 2 = l2Sq Z.field := by
  rw [← Lp.norm_toLp Z.field Z.memLp]
  exact norm_toLp_sq_eq_l2Sq Z

/-- Every individual first derivative is bounded by the L² plus Laplacian
energy, by integration by parts and the elementary quadratic Young inequality. -/
theorem directional_l2Sq_le (Z : SmoothL2Field Space) (i : Fin 3) :
    l2Sq (Z.directionalField (axis i)).field ≤ l2Sq Z.field + laplacianSq Z.field := by
  have hsingle : ‖(Z.directionalField (axis i)).toLp‖ ^ 2 ≤
      ∑ j : Fin 3, ‖(Z.directionalField (axis j)).toLp‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 3 => ‖(Z.directionalField (axis j)).toLp‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hibp := laplacian_pairing Z
  have hcs := abs_real_inner_le_norm Z.toLp (laplacianField Z).toLp
  have hneg := neg_le_abs ⟪Z.toLp, (laplacianField Z).toLp⟫
  have hy := sq_nonneg (‖Z.toLp‖ - ‖(laplacianField Z).toLp‖)
  have hn : ‖(Z.directionalField (axis i)).toLp‖ ^ 2 ≤
      ‖Z.toLp‖ ^ 2 + ‖(laplacianField Z).toLp‖ ^ 2 := by
    nlinarith [sq_nonneg ‖Z.toLp‖, sq_nonneg ‖(laplacianField Z).toLp‖]
  rw [norm_toLp_sq_eq_l2Sq, norm_toLp_sq_eq_l2Sq,
    norm_toLp_sq_eq_l2Sq, laplacianField_eq_lap] at hn
  exact hn

/-- Each second derivative is a nonnegative summand of the exact Hessian /
Laplacian identity. -/
theorem secondDirectional_l2Sq_le (Z : SmoothL2Field Space) (i j : Fin 3) :
    l2Sq ((Z.directionalField (axis i)).directionalField (axis j)).field ≤
      l2Sq Z.field + laplacianSq Z.field := by
  have hh := A05.integral_hessian_le (show A05.SmoothL2 Z.field from
    ⟨Z.smooth, Z.integrable⟩) j i
  have hz : 0 ≤ l2Sq Z.field := integral_nonneg (fun _ => sq_nonneg _)
  change (∫ x, ‖A05.dirDeriv j (A05.dirDeriv i Z.field) x‖ ^ 2) ≤ _
  change (∫ x, ‖A05.dirDeriv j (A05.dirDeriv i Z.field) x‖ ^ 2) ≤ laplacianSq Z.field at hh
  linarith

/-- The single bound controls every weak derivative at orders zero, one and
two. The weak derivative witnesses are the actual smooth directional fields. -/
theorem weakDerivsL2Bound_two (Z : SmoothL2Field Space) :
    D01.HasWeakDerivsL2Bound Z.field (l2Sq Z.field + laplacianSq Z.field) 2 := by
  have hzero : (eLpNorm Z.field 2 volume).toReal ^ 2 ≤
      l2Sq Z.field + laplacianSq Z.field := by
    rw [eLpNorm_toReal_sq_eq_l2Sq]
    have hl : 0 ≤ laplacianSq Z.field := integral_nonneg (fun _ => sq_nonneg _)
    linarith
  refine ⟨⟨Z.memLp, hzero⟩, fun i =>
    ⟨(Z.directionalField (coordinateVector i)).field, ?_,
      fun k ψ => D01.smoothField_weakDeriv_pairing Z i k ψ⟩⟩
  refine ⟨⟨(Z.directionalField (coordinateVector i)).memLp, ?_⟩, fun j =>
    ⟨((Z.directionalField (coordinateVector i)).directionalField (coordinateVector j)).field,
      ⟨((Z.directionalField (coordinateVector i)).directionalField (coordinateVector j)).memLp, ?_⟩,
      fun k ψ => D01.smoothField_weakDeriv_pairing (Z.directionalField (coordinateVector i)) j k ψ⟩⟩
  · rw [eLpNorm_toReal_sq_eq_l2Sq]
    exact directional_l2Sq_le Z i
  · rw [eLpNorm_toReal_sq_eq_l2Sq]
    exact secondDirectional_l2Sq_le Z i j

/-- The original C01 order-two Sobolev comparison, with explicit `CH2 = 16`.
The left side is the infimum over genuine angular Sobolev data. -/
theorem sobolevTwoFourier (z : A02.SpatialField) (hz : A02.MemHInfty z) :
    D01.sobolevENorm 2 z ^ (2 : ℝ) ≤ ENNReal.ofReal (16 * (l2Sq z + laplacianSq z)) := by
  have hj := D01.memHInfty_iff_smoothSquareIntegrableJets.mp hz
  let Z : SmoothL2Field Space := ⟨z, hj.1, hj.2⟩
  obtain ⟨A, hA, hnorm⟩ := D01.exists_isSobolevDatum_norm_le_sharp 2 z
    (l2Sq z + laplacianSq z) (weakDerivsL2Bound_two Z)
  have he := D01.sobolevENorm_le_of_isSobolevDatum hA
  have hs := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two] at hs
  norm_num at hnorm
  exact hs.trans (ENNReal.ofReal_le_ofReal hnorm)

end NSFormalization.Section4.C01
