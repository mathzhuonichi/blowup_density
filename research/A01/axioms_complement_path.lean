import NSFormalization.Section4.A01.ComplementPath
import Euler.SmoothL2Series
import NSFormalization.Section4.A04.ZeroSolution

#print axioms NSFormalization.Section4.A01.ComplementPath.unprojectedResidualPath
#print axioms NSFormalization.Section4.A01.ComplementPath.unprojectedResidualPath_apply
#print axioms NSFormalization.Section4.A01.ComplementPath.unprojectedResidualPath_contDiffOn
#print axioms NSFormalization.Section4.A01.ComplementPath.datumPhysical
#print axioms NSFormalization.Section4.A01.ComplementPath.datumPhysical_smooth
#print axioms NSFormalization.Section4.A01.ComplementPath.datumPhysical_rightInverse
#print axioms NSFormalization.Section4.A01.ComplementPath.datumPhysical_datum
#print axioms NSFormalization.Section4.A01.ComplementPath.complement_contDiffOn
#print axioms NSFormalization.Section4.A01.ComplementPath.complement_datum
#print axioms NSFormalization.Section4.A01.ComplementPath.map_residual
#print axioms NSFormalization.Section4.A01.ComplementPath.residual_fixed
#print axioms NSFormalization.Section4.A01.ComplementPath.advection_invariant
#print axioms NSFormalization.Section4.A01.ComplementPath.unprojectedResidualPath_invariant
#print axioms NSFormalization.Section4.A01.ComplementPath.residualOrdinaryPath
#print axioms NSFormalization.Section4.A01.ComplementPath.residual_datumPath
#print axioms NSFormalization.Section4.A01.ComplementPath.residual_restrict_six
#print axioms NSFormalization.Section4.A01.ComplementPath.residualOrdinaryPath_eq
#print axioms NSFormalization.Section4.A01.ComplementPath.complementCarrier
#print axioms NSFormalization.Section4.A01.ComplementPath.complementCarrier_paths
#print axioms NSFormalization.Section4.A01.ComplementPath.complementCarrier_identity
#print axioms NSFormalization.Section4.A01.ComplementPath.complementCarrier_joint
#print axioms NSFormalization.Section4.A01.ComplementPath.fieldDerivative_lift
#print axioms NSFormalization.Section4.A01.ComplementPath.lift_smooth
#print axioms NSFormalization.Section4.A01.ComplementPath.sliceLaplacian
#print axioms NSFormalization.Section4.A01.ComplementPath.laplacian_value_sum
#print axioms NSFormalization.Section4.A01.ComplementPath.laplacian_value_lift_ae
#print axioms NSFormalization.Section4.A01.ComplementPath.advection_value_lift_ae
#print axioms NSFormalization.Section4.A01.ComplementPath.ae_of_lift_ae
#print axioms NSFormalization.Section4.A01.ComplementPath.residualOrdinaryPath_physical
#print axioms NSFormalization.Section4.A01.ComplementPath.residualCarrier
#print axioms NSFormalization.Section4.A01.ComplementPath.residualCarrier_paths
#print axioms NSFormalization.Section4.A01.ComplementPath.residualDatum
#print axioms NSFormalization.Section4.A01.ComplementPath.residualCarrier_physical
#print axioms NSFormalization.Section4.A01.ComplementPath.residualDatum_physical
#print axioms NSFormalization.Section4.A01.ComplementPath.residualDatum_physicalSlice
#print axioms NSFormalization.Section4.A01.ComplementPath.physicalComplement
#print axioms NSFormalization.Section4.A01.ComplementPath.exists_complement_paths
#print axioms NSFormalization.Section4.A01.ComplementPath.exists_complement_joint_representative

#print axioms NSFormalization.Section4.A01.exists_complement_paths
#print axioms NSFormalization.Section4.A01.exists_complement_joint_representative

noncomputable section
open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4 NSFormalization.Section4.A01
open NSFormalization.Section4.A01.ComplementPath
open scoped ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Non-vacuity on the genuine zero force / zero cylinder pair over [0,1].
-- The main supply theorem, not just the abstract complement helper, is instantiated.
set_option maxHeartbeats 400000 in
example :
    ∃ w : ℝ → (Space → Space),
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) 1) ∧
        ∀ t : Icc (0 : ℝ) 1, IsSobolevDatum (m : ℝ) (w t.1) (G t.1)) ∧
      ∀ t : Icc (0 : ℝ) 1, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0 (fun _ : Space => (0 : Space)) A ∧
        IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 A) := by
  let hf := A04.memForceR_zero
  let F := C01.forcePath (S := 1) hf
  let hF := C01.forcePath_jetLp_continuous (S := 1) hf
  have hFz (t : Icc (0 : ℝ) 1) : F t = (zeroField : SmoothL2Field Space) := by
    apply EulerOrdinarySobolev.field_ext
    rfl
  have ha0 (q : ℕ) : ordinarySobolev q (zeroField : SmoothL2Field Space).toLp
      (zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
    apply value_injective 1
    calc
      value 1 (ordinarySobolev q (zeroField : SmoothL2Field Space).toLp
          (zeroField : SmoothL2Field Space).translation_contDiff) =
          ordinaryLift (zeroField : SmoothL2Field Space).toLp := ordinarySobolev_value q _ _
      _ = ordinaryLift 0 := congrArg ordinaryLift EulerSmoothL2Series.zeroField_value
      _ = value 1 (0 : SobolevSpace 1 q) := rfl
  have hf0 (q : ℕ) : sobolevPath F hF q = 0 := by
    apply ContinuousMap.ext
    intro t
    change ordinarySobolev q (F t).toLp (F t).translation_contDiff = 0
    rw [hFz]
    exact ha0 q
  have hpairs : ∀ q (hq : 6 ≤ q),
      ∃ u : C(Icc (0 : ℝ) 1, SobolevSpace 1 (q + 1)),
        (∀ t, ordinaryLift ((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) (zeroField : SmoothL2Field Space).toLp
            (zeroField : SmoothL2Field Space).translation_contDiff) u t := by
    intro q hq
    refine ⟨0, fun t => by simp [value], fun t => ?_, fun θ t => by simp, ?_⟩
    · exact (divergenceFreeSpace 1 1 0).zero_mem
    · intro t
      rw [ha0, hf0]
      simp [quadraticDuhamel, source_eq]
  obtain ⟨w, hw, hi⟩ := exists_complement_paths hf (by norm_num) (by norm_num)
    zeroField 0 hpairs
  refine ⟨w, hw, fun t => ?_⟩
  obtain ⟨A, hA, hC⟩ := hi t
  refine ⟨A, ?_, hC⟩
  have he := residualCarrier_physical hf (by norm_num) (by norm_num)
    zeroField 0 hpairs t (fun _ => 0) contDiff_const
    (Lp.coeFn_zero Space 2 volume).symm
  have he' : (⇑(residualCarrier hf (by norm_num) (by norm_num) zeroField 0 hpairs t))
      =ᵐ[volume] (fun _ : Space => (0 : Space)) := by
    apply he.trans
    filter_upwards with x
    change (1 : ℝ) • sliceLaplacian (fun _ : Space => (0 : Space)) x +
      ((0 : Space) - fderiv ℝ (fun _ : Space => (0 : Space)) x 0) = 0
    simp [sliceLaplacian]
  exact IsSobolevDatum.congr_field hA he'

end
