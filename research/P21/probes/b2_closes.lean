import NSFormalization.Section3.T11.EnstrophyInequality
#check NSFormalization.Section3.T11.inhomogeneousEnergyIdentityT
#check NSFormalization.Section3.T11.lintegral_convection_holder_632T
#check NSFormalization.Section3.T11.eLpNorm_three_interpolationT
#check NSFormalization.Section3.T11.young_quarticT
#check NSFormalization.Section3.T11.young_three_quartersT
#check NSFormalization.Section3.T11.young_two_factorsT
#check NSFormalization.Section3.T11.weighted_cubic_assemblyT
#check NSFormalization.Section3.T11.gradient_six_le_laplacian_twoT
#check NSFormalization.Section3.T11.convection_interpolationT
#check NSFormalization.Section3.T11.velocity_six_le_localized_gradientT

open NSFormalization.Section3.T11
example {C Y Z ε : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hε : 0 < ε) :
    C * Y ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) ≤ ε * Z + C ^ 4 / ε ^ 3 * Y ^ 3 :=
  young_three_quartersT hC hY hZ hε

-- Ordinary energy can be positive when all spatial derivatives vanish.
example {ν U F P d : ℝ} (hν : 0 < ν) (hU : 0 ≤ U) (hF : 0 ≤ F)
    (hd : d = 2 * P) (hP : P ≤ Real.sqrt U * Real.sqrt F) :
    d + ν * U ≤ (1 + ν) * (1 + U) ^ 3 + (1 + 2 / ν) * F := by
  have h := weighted_cubic_assemblyT (Y := U) (Z := U) (C := 0) (G := 0) (L := 0) (N := 0) (Q := 0)
    hν le_rfl hU le_rfl le_rfl hF (by ring) (by simp) (by simpa using hd)
    (by simp) hP (by simp)
  simpa using h

#check velocity_six_le_gradient_twoT
#check weightedEnergyIdentityT
#check convection_boundT
#check enstrophy_differential_of_norm_bridgesT
#check enstrophy_differentialT
#check enstrophy_differential_on_IccT

noncomputable section
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T12 NSFormalization.Section3.T20
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ContDiff ENNReal

private theorem zeroDatum (s : ℝ) :
    IsPeriodicDatum s (0 : SpatialField) (0 : PeriodicSobolev s) := by
  refine ⟨fun _ _ => rfl, integrable_const 0, ?_⟩
  intro i k
  change (0 : ℂ) = periodicFrequencyWeight k ^ (s / 2) •
    periodicFourierCoeff (fun _ : Space => (0 : ℂ)) k
  rw [periodicFourierCoeff_const]
  simp

private theorem zeroNorm (s : ℝ) : periodicSobolevENorm s (0 : SpatialField) = 0 := by
  rw [periodicSobolevENorm_eq (zeroDatum s)]
  change ‖(0 : PeriodicVectorData)‖ₑ = 0
  exact enorm_zero

private def zeroSolution : ClassicalSolutionT 1 0 0 2 where
  velocity := 0
  pressure := 0
  horizon_pos := by norm_num
  velocity_smooth := contDiff_const.contDiffOn
  pressure_smooth := contDiff_const.contDiffOn
  initial := by simp
  divergence := by intros; simp [spatialDivergence, spatialDerivative]
  momentum := by
    intros
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative,
      advection, spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun _ _ => zeroDatum m⟩
  pressure_gradient := by
    intro t ht
    have he : (fun x : Space => pressureGradient (0 : NSFormalization.Section4.A02.SpaceTimeScalar) t x) = 0 := by
      funext x
      simp [pressureGradient]
    rw [he]
    change MemLp (fun _ : PeriodicTorus => (0 : Space)) 2 periodicTorusMeasure
    exact memLp_const 0
  velocity_periodic := fun _ _ _ _ => rfl
  pressure_periodic := fun _ _ _ _ => rfl
  pressure_gauge := by intros; simp [PressureGaugeT, pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]

private theorem zeroForce : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, fun _ _ _ _ => rfl, ∅, isCompact_empty, empty_subset _, ?_⟩
  simp

-- The final theorem is instantiated on an actual classical solution and a
-- nonempty compact interval, with all three norm bridges discharged.
example : ∀ t ∈ Icc (1 / 2 : ℝ) 1,
    let Cν := (2 * convectionConstT) ^ 4 / (1 / 2) ^ 3 + (1 + 1) + (1 + 2 / 1)
    deriv (fun q => (periodicSobolevENorm 1 (fun x => zeroSolution.velocity (q, x))).toReal ^ 2) t +
      (periodicSobolevENorm 2 (fun x => zeroSolution.velocity (t, x))).toReal ^ 2 ≤
      Cν * (1 + (periodicSobolevENorm 1 (fun x => zeroSolution.velocity (t, x))).toReal ^ 2) ^ 3 +
        Cν * lTwoSqT 0 := by
  have hz (s : ℝ) : gradientTensor (0 : SpatialField) = 0 := by
    ext i j
    simp [gradientTensor, NSFormalization.Section4.A05.gradTensor,
      NSFormalization.Section4.A05.dirDeriv]
  have hd (i : Fin 3) : NSFormalization.Section4.A05.dirDeriv i (0 : SpatialField) = 0 := by
    funext x
    simp [NSFormalization.Section4.A05.dirDeriv]
  have hl : laplacian (0 : SpatialField) = 0 := by
    funext x
    simp only [laplacian, NSFormalization.Section4.A05.lap, hd, Pi.zero_apply, Finset.sum_const_zero]
  have hu : lTwoSqT (0 : SpatialField) = 0 := by
    change (eLpNorm (fun _ : PeriodicTorus => (0 : Space)) 2 periodicTorusMeasure).toReal ^ 2 = 0
    simp
  have hg : gradientSqT (0 : SpatialField) = 0 := by
    rw [gradientSqT, hz 0]
    change (eLpNorm (fun _ : PeriodicTorus => (0 : WithLp 2 (Fin 3 → Space))) 2 periodicTorusMeasure).toReal ^ 2 = 0
    simp
  have hL : laplacianSqT (0 : SpatialField) = 0 := by
    change lTwoSqT (laplacian (0 : SpatialField)) = 0
    rw [hl, hu]
  have h := enstrophy_differential_on_IccT zeroSolution zeroForce (by norm_num)
    (r := 1 / 2) (s := 1) (by norm_num) (by norm_num)
    (by intro q hq; change (periodicSobolevENorm 1 (0 : SpatialField)).toReal ^ 2 = _
        change _ = lTwoSqT (0 : SpatialField) + gradientSqT (0 : SpatialField)
        rw [zeroNorm, hu, hg]; norm_num)
    (by intro t ht; change (periodicSobolevENorm 2 (0 : SpatialField)).toReal ^ 2 ≤
          lTwoSqT (0 : SpatialField) + 2 * gradientSqT (0 : SpatialField) + laplacianSqT (0 : SpatialField)
        rw [zeroNorm, hu, hg, hL]; norm_num)
    (by intro t ht; change periodicLpENorm 2 (gradientTensor (0 : SpatialField)) ≤
          ENNReal.ofReal (Real.sqrt (gradientSqT (0 : SpatialField)))
        rw [hz 0, hg]
        change eLpNorm (fun _ : PeriodicTorus => (0 : WithLp 2 (Fin 3 → Space))) 2 periodicTorusMeasure ≤ _
        simp)
  intro t ht
  have hh := h t ht
  dsimp only at hh ⊢
  simpa only [one_mul, Pi.zero_apply, ← Pi.zero_def] using hh

-- Mutation: removing -2νL from the energy identity destroys absorption.
-- At ν=1, C=U=G=F=N=P=Q=d=0 and L=Z=3, every other scalar premise holds,
-- but the proposed conclusion is 3 ≤ 2. This is a semantic counterexample.
/-- error: unsolved goals
⊢ False -/
#guard_msgs (error) in
example : (0 : ℝ) + 1 * 3 ≤
    ((2 * 0) ^ 4 / (1 / 2) ^ 3 + (1 + 1)) * (1 + 0) ^ 3 + (1 + 2 / 1) * 0 := by
  exact weighted_cubic_assemblyT (ν := 1) (C := 0) (U := 0) (G := 0)
    (L := 3) (F := 0) (N := 0) (P := 0) (Q := 0) (d := 0) (Y := 0) (Z := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : ¬ ((0 : ℝ) + 1 * 3 ≤
    ((2 * 0) ^ 4 / (1 / 2) ^ 3 + (1 + 1)) * (1 + 0) ^ 3 + (1 + 2 / 1) * 0) := by
  norm_num
