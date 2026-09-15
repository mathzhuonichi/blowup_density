import NSFormalization.Section4.A01.JointRepresentative

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.D01
open scoped ContDiff

#print axioms boundedEvaluation_hasFDerivWithinAt
#print axioms denseRange_angularDatum
#print axioms angularDirectionalDerivative_angularDatum
#print axioms angularBoundedRepresentative_angularDatum
#print axioms angularRepresentativeGradient
#print axioms angularRepresentativeGradient_apply
#print axioms angularBoundedRepresentative_hasFDerivAt
#print axioms angularBoundedRepresentative_contDiff
#print axioms angularEvaluation
#print axioms boundedContinuousEvaluation_continuous
#print axioms scalarJointRepresentative
#print axioms scalarJointRepresentative_contDiffOn
#print axioms vectorRepresentative
#print axioms vectorJointRepresentative
#print axioms vectorJointRepresentative_contDiffOn
#print axioms vectorRepresentative_ae
#print axioms vectorRepresentative_continuous
#print axioms vectorRepresentative_eq_of_datums
#print axioms vectorJointRepresentative_eqOn_of_datums
#print axioms jointRepresentative
#print axioms jointRepresentative_slice
#print axioms vectorJointRepresentative_contDiffOn_of_compatible
#print axioms jointRepresentative_contDiffOn_nat
#print axioms jointRepresentative_contDiffOn
#print axioms exists_joint_smooth_representative
#print axioms exists_joint_smooth_representative_of_hall

-- Non-vacuity: R4 applies to the explicitly assigned zero ordinary path.
example :
    ∃ u : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) 1,
        (fun x => u (↑t, x)) =ᵐ[volume]
          ⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) ∧
      ContDiffOn ℝ ∞ u
        (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  apply exists_joint_smooth_representative (S := 1) (by norm_num)
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
  intro j m
  refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
  intro t
  simp only [ContinuousMap.zero_apply]
  apply IsSobolevDatum.congr_field (isSobolevDatum_zero (m : ℝ))
  exact (Lp.coeFn_zero Space 2 volume).symm

end
