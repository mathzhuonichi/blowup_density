import NSFormalization.Section4.A01.PressureRegularity
import NSFormalization.Section4.A04.ZeroSolution

/-! Axiom audit and positive-horizon satisfiability of the complement-representative helper.
The separate pipeline probe exercises the complete pressure supply. -/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (memForceR_zero)
open scoped ContDiff

namespace NSFormalization.Section4.A01

#print axioms lerayComplement_longitudinal
#print axioms longitudinal_symm_of_longitudinal
#print axioms tempered_antisym_eq_of_fourier_longitudinal
#print axioms curl_free_of_orderZeroDatum_longitudinal
#print axioms hasSymmetricJacobian_of_lerayComplement_orderZeroDatum
#print axioms memLp_of_isSobolevDatum_zero
#print axioms pressureSupply_of_pieces
#print axioms pressureGradientOfVelocity_eq_of_slices
#print axioms carrierDatum_physicalSlice
#print axioms exists_smooth_lerayComplement_representative

example : ∃ G : A02.SpaceTimeField,
    (∀ t : Icc (0 : ℝ) 1, (fun x => G (t.1, x)) =ᵐ[volume] (0 : Space → Space)) ∧
    (ContDiffOn ℝ ∞ G (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) ∧
      ∀ t ∈ Ico (0 : ℝ) 1, MemLp (fun x => G (t, x)) 2 volume ∧
        RadialPotential.HasSymmetricJacobian (fun x => G (t, x))) := by
  have hz : ∀ t : Icc (0 : ℝ) 1,
      (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) =ᵐ[volume]
        (0 : Space → Space) := by
    intro t
    exact Lp.coeFn_zero _ _ _
  obtain ⟨G, hslice, hG⟩ := exists_smooth_lerayComplement_representative
    (S := 1) (by norm_num) 0
    (by
      intro j m
      refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
      intro t
      exact IsSobolevDatum.congr_field (isSobolevDatum_zero (m : ℝ)) (hz t).symm)
    (fun _ => 0)
    (by
      intro t
      simpa using IsSobolevDatum.congr_field (isSobolevDatum_zero 0) (hz t).symm)
  exact ⟨G, fun t => (hslice t).trans (hz t), hG⟩

end NSFormalization.Section4.A01
