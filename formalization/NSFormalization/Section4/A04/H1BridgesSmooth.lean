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

end NSFormalization.Section4.A04
