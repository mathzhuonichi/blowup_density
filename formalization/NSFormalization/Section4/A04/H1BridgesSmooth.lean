import NSFormalization.Section4.A04.H1Bridges
import NSFormalization.Section4.C01.SobolevTwo

/-!
Support-free angular Sobolev energy identities for P21 Route B.
The registered angular convention cancels the cycles Fourier factor `2π`.
These bridges serve the separate H¹ restart obligation; the revised article
`02-preliminaries.tex:149–156` states local existence and integral continuation.
-/
noncomputable section
namespace NSFormalization.Section4.A04
open Set MeasureTheory NavierStokes.ProblemStatement
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NSFormalization.Source NSFormalization.Source.RealSobolev NSFormalization.Paper3
open NSFormalization.Section4.D01 NSFormalization.Section4.C01
open scoped ENNReal

/-- Exact raising identity on smooth square-integrable fields, without support assumptions. -/
theorem sobolevEnergy_succ_smooth (Z : SmoothL2Field Space) (m : ℕ) :
    (sobolevENorm ((m : ℝ) + 1) Z.field).toReal ^ 2 =
      (sobolevENorm (m : ℝ) Z.field).toReal ^ 2 +
        ∑ j : Fin 3, (sobolevENorm (m : ℝ)
          (Z.directionalField (coordinateVector j)).field).toReal ^ 2 := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_of_memLp_derivs m Z.field (weakDerivs_smooth m Z)
  have hex j := exists_isSobolevDatum_of_memLp_derivs m
    (Z.directionalField (coordinateVector j)).field
    (weakDerivs_smooth m (Z.directionalField (coordinateVector j)))
  choose C hC using hex
  have hw := smoothField_weakDeriv_pairing Z
  have hg := fun i => raisableWitness_of_memLp_smul _
    (fun j => memLp_coord_smul_datum hA hC hw i j)
  rw [A03.sobolevENorm_eq (isSobolevDatum_raise hA hg),
    A03.sobolevENorm_eq hA, toReal_enorm, toReal_enorm]
  simp_rw [A03.sobolevENorm_eq (hC _), toReal_enorm]
  exact norm_raise_sq_eq hA hC hw hg

/-- Order zero is the physical energy on a smooth L² field. -/
theorem sobolevEnergy_zero_smooth (Z : SmoothL2Field Space) :
    (sobolevENorm 0 Z.field).toReal ^ 2 = l2Sq Z.field := by
  rw [NSFormalization.Section3.T22.sobolevENorm_zero_eq_eLpNorm Z.memLp]
  exact eLpNorm_toReal_sq_eq_l2Sq Z

/-- The angular H¹ energy equals the unweighted physical energy plus gradient. -/
theorem sobolevEnergy_one_smooth (Z : SmoothL2Field Space) :
    (sobolevENorm 1 Z.field).toReal ^ 2 = l2Sq Z.field + gradientSq Z.field := by
  have h := sobolevEnergy_succ_smooth Z 0
  simp only [Nat.cast_zero, zero_add, sobolevEnergy_zero_smooth] at h
  rw [h]
  congr 1
  simpa only [norm_toLp_sq_eq_l2Sq, l2Sq, gradientSq, axis, coordinateVector] using gradientSq_eq_sum Z

/-- The exact H² identity, including all low-frequency terms. -/
theorem sobolevEnergy_two_smooth (Z : SmoothL2Field Space) :
    (sobolevENorm 2 Z.field).toReal ^ 2 =
      l2Sq Z.field + 2 * gradientSq Z.field + laplacianSq Z.field := by
  have h := sobolevEnergy_succ_smooth Z 1
  norm_num only [Nat.cast_one, one_add_one_eq_two] at h
  rw [h]
  simp_rw [sobolevEnergy_one_smooth]
  rw [Finset.sum_add_distrib]
  have hg : (∑ j : Fin 3, l2Sq (Z.directionalField (coordinateVector j)).field) =
      gradientSq Z.field := by
    simpa only [norm_toLp_sq_eq_l2Sq, l2Sq, gradientSq, axis, coordinateVector]
      using gradientSq_eq_sum Z
  have hh : (∑ j : Fin 3, gradientSq (Z.directionalField (coordinateVector j)).field) =
      laplacianSq Z.field := by
    have he (j : Fin 3) : (Z.directionalField (coordinateVector j)).field =
        A05.dirDeriv j Z.field := rfl
    have hdir (j : Fin 3) : gradientSq (Z.directionalField (coordinateVector j)).field =
        ∑ i : Fin 3, ∫ x, ‖A05.dirDeriv i (A05.dirDeriv j Z.field) x‖ ^ 2 := by
      have hh := (gradientSq_eq_sum (Z.directionalField (coordinateVector j))).symm
      simp only [norm_toLp_sq_eq_l2Sq, directionalField_field] at hh
      rw [he] at hh
      rw [he]
      simpa only [gradientSq, A05.dirDeriv, axis, coordinateVector] using hh
    simp_rw [hdir]
    rw [Finset.sum_comm]
    exact A05.sum_integral_hessian ⟨Z.smooth, Z.integrable⟩
  rw [hg, hh]
  ring

/-- The Frobenius gradient norm is the square root of B1's gradient energy. -/
theorem eLpNorm_gradTensor_eq_sqrt (Z : SmoothL2Field Space) :
    eLpNorm (A05.gradTensor Z.field) 2 volume =
      ENNReal.ofReal (Real.sqrt (gradientSq Z.field)) := by
  have he (x : Space) : ‖A05.gradTensor Z.field x‖ ^ 2 =
      ∑ i : Fin 3, ‖fderiv ℝ Z.field x (coordinateVector i)‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hi : Integrable (fun x => ‖A05.gradTensor Z.field x‖ ^ 2) volume := by
    simp_rw [he]
    exact integrable_finsetSum _ (fun i _ =>
      field_normSq_integrable (Z.directionalField (coordinateVector i)))
  rw [I02.eLpNorm_two_eq_ofReal_sqrt hi]
  simp only [he, gradientSq]

end NSFormalization.Section4.A04
