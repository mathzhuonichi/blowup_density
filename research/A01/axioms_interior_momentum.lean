import NSFormalization.Section4.A01.InteriorMomentum

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open NSFormalization.Paper3
open scoped ContDiff

#print axioms vectorRepresentative_sub
#print axioms vectorRepresentative_hasDerivAt
#print axioms jointRepresentative_temporalDerivative
#print axioms ae_eq_of_isSobolevDatum_locInt
#print axioms ae_eq_of_isSobolevDatum
#print axioms jointRepresentative_temporalDerivative_of_cylinder
#print axioms pressureGradientOfVelocity_contDiffOn_interior
#print axioms interior_momentum_identity_of_datums
#print axioms interior_momentum_identity
#print axioms interior_momentum_identity_of_complement_paths

-- Non-vacuity of the generic derivative interface: explicit zero ordinary
-- path and zero order-two datum path, at every strictly interior time.
example : ∃ hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
    ContDiffOn ℝ j H (Icc (0 : ℝ) 1) ∧
    ∀ t : Icc (0 : ℝ) 1,
      IsSobolevDatum (m : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (H t.1),
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      temporalDerivative (jointRepresentative 0 hpaths) t x = 0 := by
  have hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j H (Icc (0 : ℝ) 1) ∧
      ∀ t : Icc (0 : ℝ) 1,
        IsSobolevDatum (m : ℝ)
          (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (H t.1) := by
    intro j m
    refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
    intro t
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero (m : ℝ))
    exact (Lp.coeFn_zero Space 2 volume).symm
  refine ⟨hpaths, ?_⟩
  intro t ht x
  have hdatum : ∀ r : Icc (0 : ℝ) 1,
      IsSobolevDatum 2
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) r))
        (0 : RealVectorSobolev 2) := by
    intro r
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero 2)
    exact (Lp.coeFn_zero Space 2 volume).symm
  have hd := jointRepresentative_temporalDerivative (by norm_num : (2 : ℝ) ≤ 2)
    0 hpaths (fun _ => 0) hdatum ht 0 (hasDerivWithinAt_const t _ 0) x
  rw [hd]
  apply PiLp.ext
  intro i
  simp [vectorRepresentative]

-- Non-vacuity of order-zero assembly: zero force, velocity and complement.
example (ν : ℝ) : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
    (0 : VelocityField) (t, x) = pressureGradientOfVelocity ν 0 0 (t, x) := by
  apply interior_momentum_identity_of_datums ν 0 0 0
    contDiffOn_const contDiffOn_const contDiffOn_const (fun _ => 0)
  · intro t ht
    simp only [map_zero]
    exact isSobolevDatum_zero 0
  · intro t
    simpa [momentumResidualOfVelocity, advection, spatialLaplacian, spatialDerivative]
      using isSobolevDatum_zero 0
  · intro t ht
    simpa [temporalDerivative] using isSobolevDatum_zero 0

open NSFormalization.Source.ForcedCylinderLocal
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerQuadraticSource EulerVolterraConvolution

-- Non-vacuity of the complete exported cylinder assembly at order m = 2,
-- q = 6, viscosity = 1 and horizon = 1. Every named input is discharged.
example : ∃ hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
    ContDiffOn ℝ j H (Icc (0 : ℝ) 1) ∧
    ∀ t : Icc (0 : ℝ) 1,
      IsSobolevDatum (m : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (H t.1),
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      (0 : VelocityField) (t, x) =
        pressureGradientOfVelocity 1 0 (jointRepresentative 0 hpaths) (t, x) := by
  have hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j H (Icc (0 : ℝ) 1) ∧
      ∀ t : Icc (0 : ℝ) 1,
        IsSobolevDatum (m : ℝ)
          (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (H t.1) := by
    intro j m
    refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
    intro t
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero (m : ℝ))
    exact (Lp.coeFn_zero Space 2 volume).symm
  refine ⟨hpaths, ?_⟩
  have hB : ∀ t : Icc (0 : ℝ) 1,
      IsSobolevDatum 2 (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t))
        ((0 : C(Icc (0 : ℝ) 1, RealVectorSobolev 2)) t) := by
    intro t
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero 2)
    exact (Lp.coeFn_zero Space 2 volume).symm
  have hzero (t : Icc (0 : ℝ) 1) :
      (fun x => jointRepresentative 0 hpaths (t.1, x)) = 0 := by
    change vectorRepresentative 2 (by norm_num)
      (Classical.choose (hpaths 0 2) t.1) = 0
    have heq : vectorRepresentative 2 (by norm_num)
        (Classical.choose (hpaths 0 2) t.1) =
        vectorRepresentative 2 (by norm_num) 0 :=
      vectorRepresentative_eq_of_datums (by norm_num) (by norm_num)
        ((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)
        ((Classical.choose_spec (hpaths 0 2)).2 t) (hB t)
    rw [heq]
    funext x
    apply PiLp.ext
    intro i
    simp [vectorRepresentative]
  refine interior_momentum_identity (q := 6) (m := 2) (by norm_num) (by norm_num)
    (by norm_num) (ν := 1) (S := 1) (by norm_num) (by norm_num)
    0 0 0 0 (fun t => by simp [value])
    (fun t => by simp [quadraticDuhamel, source_eq]) hpaths 0 0 hB ?_
    0 0 contDiffOn_const contDiffOn_const (fun _ => 0) (fun _ => 0) ?_ ?_ ?_ ?_
  · intro t
    have hz : ordinaryResidualPath (by norm_num : 6 ≤ 6)
        (by norm_num : 2 + 2 ≤ 6 + 1) 1
        (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)) 0 t = 0 := by
      change ordinaryLift.toContinuousLinearMap.adjoint
        (value 1 (cylinderResidual (by norm_num : 6 ≤ 6)
          (by norm_num : 2 + 2 ≤ 6 + 1) 1
          (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)) 0 t)) = 0
      rw [cylinderResidual_value]
      simp [source_eq, value]
    rw [hz]
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero 2)
    exact (Lp.coeFn_zero Space 2 volume).symm
  · intro t
    simp only [map_zero]
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero 0)
    exact (Lp.coeFn_zero Space 2 volume).symm
  · intro t
    exact (Lp.coeFn_zero Space 2 volume).symm
  · intro t
    simpa [momentumResidualOfVelocity, NavierStokes.ProblemStatement.advection,
      spatialLaplacian, spatialDerivative, hzero t] using isSobolevDatum_zero 0
  · intro t ht
    simp

end
